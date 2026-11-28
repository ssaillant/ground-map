#!/usr/bin/env bash
# Bring the results of a search run to main through a pull request.
# Called by .github/workflows/search.yml; nothing here runs a search.
#
#   publish_results.sh check-token     fail unless RESULTS_PR_TOKEN can read the repository,
#                                      read pull requests and push (creates nothing)
#   publish_results.sh prepare PARTS   choose the base commit, merge the per-seed results in
#                                      PARTS into results/, re-verify the models, regenerate
#                                      docs/results.md, and commit
#   publish_results.sh publish         push that commit with RESULTS_PR_TOKEN and open the
#                                      pull request (or report the one already open)
#
# Base commit (prepare):
#   - the run's commit is already in main (a run started on main, or on a search branch that
#     has been merged): the results are merged onto the current main and go to a new branch
#     results/run-<run id>, so the pull request contains results/ and docs/results.md only;
#   - otherwise (the run's branch has commits main does not have): the results are committed
#     on top of that branch, as before, and the pull request is the branch's own, so it
#     carries the branch's unmerged commits too.
# The push and the pull request use RESULTS_PR_TOKEN because events caused by the
# workflow's own GITHUB_TOKEN do not start other workflows, and main requires the
# "isabelle" check of check.yml to have run on the pull request.
#
# Environment: REPO (owner/name), RUN_ID, RUN_URL, RUN_SHA, REF_NAME, REF_TYPE,
# RESULTS_PR_TOKEN. GITHUB_API_URL, GITHUB_SERVER_URL and GM_PUSH_URL may be overridden
# (GM_PUSH_URL only for local tests against a file:// remote).
set -euo pipefail

: "${REPO:?}" "${RUN_ID:?}"
API="${GITHUB_API_URL:-https://api.github.com}"
SERVER="${GITHUB_SERVER_URL:-https://github.com}"
PUSH_URL="${GM_PUSH_URL:-$SERVER/$REPO.git}"
BASE=main
STATE="${RUNNER_TEMP:-/tmp}/gm-publish-$RUN_ID.env"
TMP="$(mktemp -d)"
SETUP="Repository Settings > Secrets and variables > Actions > RESULTS_PR_TOKEN"

WHAT="Search results not published"
die() { echo "::error title=$WHAT::$*" >&2; summary "**$WHAT.** $*"; exit 1; }
summary() { [ -n "${GITHUB_STEP_SUMMARY:-}" ] && printf '%s\n\n' "$*" >> "$GITHUB_STEP_SUMMARY"; return 0; }

need_token() {
  [ -n "${RESULTS_PR_TOKEN:-}" ] || die "The secret RESULTS_PR_TOKEN is missing or empty ($SETUP). It must be a fine-grained personal access token for $REPO with Contents: Read and write and Pull requests: Read and write."
}

remote() {  # push/fetch URL carrying the token (Actions masks the secret in logs)
  case "$PUSH_URL" in
    https://*) printf 'https://x-access-token:%s@%s' "$RESULTS_PR_TOKEN" "${PUSH_URL#https://}" ;;
    *) printf '%s' "$PUSH_URL" ;;
  esac
}

api() {  # api METHOD PATH [JSON-FILE]: prints the HTTP status; body in $TMP/body, headers in $TMP/headers
  local args=(-sS -X "$1" -o "$TMP/body" -D "$TMP/headers" -w '%{http_code}'
    -H "Authorization: Bearer $RESULTS_PR_TOKEN" -H "Accept: application/vnd.github+json"
    -H "X-GitHub-Api-Version: 2022-11-28")
  [ $# -ge 3 ] && args+=(-H "Content-Type: application/json" --data-binary "@$3")
  curl "${args[@]}" "$API$2" || true  # -w prints 000 when no response arrives
}

json() { python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(eval(sys.argv[2], {"d": d}) or "")' "$TMP/body" "$1"; }

registry_version() {  # registry_version COMMIT
  git show "$1:principles/registry.yaml" 2>/dev/null \
    | python3 -c 'import sys,yaml; print(yaml.safe_load(sys.stdin).get("registry_version","?"))' 2>/dev/null || echo "?"
}

check_token() {
  WHAT="Search not started: RESULTS_PR_TOKEN does not work"
  need_token
  local code; code="$(api GET "/repos/$REPO")"
  case "$code" in
    200) ;;
    401) die "GitHub rejected RESULTS_PR_TOKEN (HTTP 401): the token has expired or was revoked. Create a new one and replace the secret ($SETUP)." ;;
    403|404) die "RESULTS_PR_TOKEN cannot see $REPO (HTTP $code). Give the token access to this repository." ;;
    *) die "Unexpected HTTP $code from GitHub while checking RESULTS_PR_TOKEN." ;;
  esac
  local exp days
  exp="$(grep -i '^github-authentication-token-expiration:' "$TMP/headers" | cut -d: -f2- | tr -d '\r' | sed 's/^ *//' || true)"
  if [ -n "$exp" ]; then
    days=$(( ( $(date -u -d "$exp" +%s) - $(date -u +%s) ) / 86400 ))
    echo "RESULTS_PR_TOKEN expires $exp ($days days from now)."
    if [ "$days" -lt 14 ]; then
      echo "::warning title=RESULTS_PR_TOKEN expires soon::It expires $exp. A search that ends after that will not open its pull request. Replace the secret ($SETUP)."
    fi
  else
    echo "RESULTS_PR_TOKEN has no expiry date."
  fi
  code="$(api GET "/repos/$REPO/pulls?per_page=1")"
  [ "$code" = 200 ] || die "RESULTS_PR_TOKEN cannot read pull requests of $REPO (HTTP $code). Grant it Pull requests: Read and write."
  # A dry-run push needs write access but creates nothing.
  local probe; probe="$(mktemp -d)"
  git -C "$probe" init -q
  git -C "$probe" -c user.name=probe -c user.email=probe@invalid commit -q --allow-empty -m probe
  if ! git -C "$probe" push --dry-run -q "$(remote)" HEAD:refs/heads/results/token-probe 2>"$TMP/err"; then
    die "RESULTS_PR_TOKEN cannot push to $REPO. Grant it Contents: Read and write. git said: $(tr '\n' ' ' < "$TMP/err")"
  fi
  echo "RESULTS_PR_TOKEN can read $REPO, read its pull requests and push to it."
  echo "(Creating pull requests cannot be tested without creating one; Pull requests: Read and write is needed.)"
}

fetch() {  # fetch BRANCH -> refs/remotes/origin/BRANCH; fails if the branch does not exist
  git fetch -q "$(remote)" "+refs/heads/$1:refs/remotes/origin/$1" 2>/dev/null
}

prepare() {
  local parts="${1:?parts directory}"
  need_token
  fetch "$BASE" || die "Could not fetch $BASE."
  local mode base_ref target
  if git merge-base --is-ancestor "$RUN_SHA" "origin/$BASE"; then
    mode=main; base_ref="origin/$BASE"; target="results/run-$RUN_ID"
  elif [ "${REF_TYPE:-}" = branch ] && fetch "$REF_NAME"; then
    mode=branch; base_ref="origin/$REF_NAME"; target="$REF_NAME"
  else
    mode=detached; base_ref="$RUN_SHA"; target="results/run-$RUN_ID"
  fi
  git checkout -q --detach "$base_ref"
  local base_sha; base_sha="$(git rev-parse HEAD)"
  python3 scripts/merge_results.py "$parts"
  python3 scripts/verify_models.py
  python3 scripts/summarize.py
  git add results docs/results.md
  local changed=0
  if ! git diff --cached --quiet; then
    git -c user.name="ground-map search" -c user.email="actions@users.noreply.github.com" \
      commit -q -m "search: results of run $RUN_ID" -m "$RUN_URL"
    changed=1
  fi
  {
    echo "MODE=$mode"; echo "BASE_SHA=$base_sha"; echo "TARGET=$target"; echo "CHANGED=$changed"
    echo "HEAD_SHA=$(git rev-parse HEAD)"
  } > "$STATE"
  echo "mode=$mode base=$base_sha target=$target changed=$changed"
}

counts() {  # counts COMMIT: class counts of results/queries.jsonl at COMMIT
  git show "$1:results/queries.jsonl" 2>/dev/null | python3 -c '
import collections, json, sys
c = collections.Counter(json.loads(l)["class"] for l in sys.stdin if l.strip())
print(", ".join(f"{k} {v}" for k, v in sorted(c.items())) or "none")'
}

body() {
  local run_reg base_reg; run_reg="$(registry_version "$RUN_SHA")"; base_reg="$(registry_version "$BASE_SHA")"
  echo "Opened automatically by the search workflow at the end of [run $RUN_ID]($RUN_URL)."
  echo
  echo "- Run started on: \`$REF_NAME\` at \`${RUN_SHA:0:7}\` (registry $run_reg)"
  case "$MODE" in
    main) echo "- Results merged onto: \`$BASE\` at \`${BASE_SHA:0:7}\` (registry $base_reg). This pull request changes results/ and docs/results.md only." ;;
    branch) echo "- Results committed on: \`$REF_NAME\` at \`${BASE_SHA:0:7}\` (registry $base_reg). **This pull request also carries the branch's commits that are not in $BASE:**"
            echo; git log --no-merges --format='  - `%h` %s' "origin/$BASE..$BASE_SHA" | head -40 ;;
    detached) echo "- The run's branch no longer exists; results committed on the run's commit. **This pull request carries every commit of that commit not in $BASE.**" ;;
  esac
  echo
  if [ "$run_reg" != "$base_reg" ]; then
    echo "**Registry versions differ.** The queries ran under registry $run_reg; the merged results are re-verified and summarised under $base_reg. Records do not carry a registry version, so check that no entry the search used has changed meaning."
    echo
  fi
  echo "Classes in results/queries.jsonl:"
  echo "- before: $(counts "$BASE_SHA")"
  echo "- after: $(counts "$HEAD_SHA")"
  echo
  echo "The per-seed records are merged by scripts/merge_results.py (one record per package; a definite class replaces unknown), the Nitpick models are re-verified by scripts/verify_models.py, and docs/results.md is regenerated by scripts/summarize.py. A seed stopped by the time limit contributes partial results. Unknown is not consistent. The required isabelle check runs on this pull request; merging is left to the reviewer."
}

publish() {
  need_token
  # shellcheck disable=SC1090
  source "$STATE"
  if [ "$CHANGED" != 1 ]; then
    echo "The run produced no new results; no pull request."
    summary "Search run $RUN_ID: no new results, so no pull request."
    return 0
  fi
  if [ "$MODE" = branch ]; then
    if ! git push -q "$(remote)" "HEAD:refs/heads/$TARGET" 2>"$TMP/err"; then
      git push -q --force "$(remote)" "HEAD:refs/heads/results/run-$RUN_ID" \
        || die "Could not push the results, either to $TARGET or to results/run-$RUN_ID: $(tr '\n' ' ' < "$TMP/err"). They are kept in the artifact results-merged of this run."
      die "$TARGET changed during the run, so the results were not added to it. They are on branch results/run-$RUN_ID. Re-run this job (Re-run failed jobs) to merge them onto the new tip of $TARGET. git said: $(tr '\n' ' ' < "$TMP/err")"
    fi
  else
    # results/run-<id> belongs to this run alone; a re-run of this job replaces it.
    git push -q --force "$(remote)" "HEAD:refs/heads/$TARGET" 2>"$TMP/err" \
      || die "Could not push the results to $TARGET: $(tr '\n' ' ' < "$TMP/err"). They are kept in the artifact results-merged of this run."
  fi
  echo "Pushed results to $TARGET."
  local code url
  code="$(api GET "/repos/$REPO/pulls?state=open&base=$BASE&head=${REPO%%/*}:$TARGET")"
  [ "$code" = 200 ] || die "Could not list pull requests (HTTP $code). The results are on branch $TARGET."
  url="$(json 'd[0]["html_url"] if d else ""')"
  if [ -n "$url" ]; then
    echo "Pull request already open: $url (updated by this push)."
    summary "Search run $RUN_ID: results pushed to \`$TARGET\`; pull request already open: $url"
    return 0
  fi
  local title="Search results: run $RUN_ID ($REF_NAME)"
  body > "$TMP/body.md"
  python3 -c 'import json,sys; print(json.dumps({"title": sys.argv[1], "head": sys.argv[2], "base": sys.argv[3], "body": open(sys.argv[4]).read(), "maintainer_can_modify": True}))' \
    "$title" "$TARGET" "$BASE" "$TMP/body.md" > "$TMP/req.json"
  code="$(api POST "/repos/$REPO/pulls" "$TMP/req.json")"
  case "$code" in
    201) url="$(json 'd["html_url"]')" ;;
    401) die "GitHub rejected RESULTS_PR_TOKEN (HTTP 401) when opening the pull request: it expired during the run. The results are on branch $TARGET; replace the secret ($SETUP) and re-run this job, or open the pull request by hand." ;;
    403) die "RESULTS_PR_TOKEN may not open pull requests (HTTP 403). Grant it Pull requests: Read and write. The results are on branch $TARGET." ;;
    *) die "Opening the pull request failed (HTTP $code): $(json 'd.get("message","")') $(json 'str(d.get("errors",""))'). The results are on branch $TARGET." ;;
  esac
  echo "Opened $url"
  summary "Search run $RUN_ID: opened $url"
}

case "${1:-}" in
  check-token) check_token ;;
  prepare) shift; prepare "$@" ;;
  publish) publish ;;
  *) echo "usage: $0 check-token | prepare PARTS | publish" >&2; exit 2 ;;
esac
