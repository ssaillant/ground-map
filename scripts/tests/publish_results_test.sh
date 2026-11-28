#!/usr/bin/env bash
# Local test of scripts/publish_results.sh: no GitHub, no Isabelle.
# A bare clone of this repository stands in for the GitHub remote and
# scripts/tests/github_stub.py for the REST API. Run from the repository root:
#   scripts/tests/publish_results_test.sh
# Needs the branches main and search/sk-d6 (a commit already in main) locally or in origin.
set -uo pipefail
ROOT="$(git rev-parse --show-toplevel)"; T="$(mktemp -d)"; PORT=8765; FAIL=0
trap 'kill $STUB 2>/dev/null; rm -rf "$T"' EXIT
rev() { git -C "$ROOT" rev-parse -q --verify "origin/$1" || git -C "$ROOT" rev-parse "$1"; }
MAIN="$(rev main)"; INMAIN="$(rev search/sk-d6)"
git init -q --bare "$T/remote.git" && git -C "$T/remote.git" symbolic-ref HEAD refs/heads/main
git -C "$ROOT" -c push.negotiate=false push -q "$T/remote.git" "$MAIN:refs/heads/main" "$INMAIN:refs/heads/search/sk-d6"
# a branch with a commit main does not have
git clone -q "$T/remote.git" "$T/seed" && git -C "$T/seed" checkout -q -b claude/x "$MAIN" \
  && git -C "$T/seed" -c user.name=t -c user.email=t@t commit -q --allow-empty -m "unmerged work" \
  && git -C "$T/seed" push -q origin claude/x
AHEAD="$(git -C "$T/seed" rev-parse HEAD)"
STUB=; stub() { kill $STUB 2>/dev/null; wait $STUB 2>/dev/null; : > "$T/requests.log"
  STUB_LOG="$T/requests.log" python3 "$ROOT/scripts/tests/github_stub.py" $PORT "$1" & STUB=$!; sleep 0.5; }
run() {  # run NAME SHA REF STUBMODE NEWRESULTS -> exit status of check-token && prepare && publish
  local w="$T/w-$1"; stub "$4"
  git clone -q "$T/remote.git" "$w" && git -C "$w" checkout -q --detach "$2"
  cp "$ROOT/scripts/publish_results.sh" "$ROOT/scripts/merge_results.py" "$w/scripts/"
  mkdir -p "$w/parts/results-seed-11" "$T/rt-$1"
  [ "$5" = yes ] && echo '{"key": "ZZ.TEST", "class": "refuted", "proof": "test", "model": null, "semantics": "v2"}' > "$w/parts/results-seed-11/queries.jsonl"
  ( cd "$w" && export REPO=o/r RUN_ID="$1" RUN_URL=u RUN_SHA="$2" REF_NAME="$3" REF_TYPE=branch \
      RESULTS_PR_TOKEN="${TOKEN-secret}" GITHUB_API_URL="http://127.0.0.1:$PORT" GM_PUSH_URL="$T/remote.git" RUNNER_TEMP="$T/rt-$1"
    scripts/publish_results.sh check-token && scripts/publish_results.sh prepare parts && scripts/publish_results.sh publish ) > "$T/out-$1" 2>&1
}
expect() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; sed 's/^/     /' "$T/out-$1" | tail -5; FAIL=1; fi; }

run inmain "$INMAIN" search/sk-d6 ok yes
expect inmain '[ $? = 0 ] && grep -q "POST /repos/o/r/pulls" "$T/requests.log" && grep -q "\"head\": \"results/run-inmain\"" "$T/requests.log" \
  && [ "$(git -C "$T/remote.git" diff --name-only main results/run-inmain | sort | tr "\n" " ")" = "docs/results.md results/queries.jsonl " ]'
run ahead "$AHEAD" claude/x ok yes
expect ahead '[ $? = 0 ] && grep -q "\"head\": \"claude/x\"" "$T/requests.log" && grep -q "unmerged work" "$T/requests.log" \
  && git -C "$T/remote.git" log -1 --format=%s claude/x | grep -q "search: results of run ahead"'
run nothing "$INMAIN" search/sk-d6 ok no
expect nothing '[ $? = 0 ] && ! grep -q POST "$T/requests.log" && grep -q "no pull request" "$T/out-nothing"'
run open "$INMAIN" search/sk-d6 open yes
expect open '[ $? = 0 ] && ! grep -q POST "$T/requests.log" && grep -q "already open" "$T/out-open"'
run expired "$INMAIN" search/sk-d6 expired yes
expect expired '[ $? != 0 ] && grep -q "HTTP 401" "$T/out-expired"'
TOKEN= run missing "$INMAIN" search/sk-d6 ok yes
expect missing '[ $? != 0 ] && grep -q "missing or empty" "$T/out-missing"'
exit $FAIL
