#!/usr/bin/env python3
"""Replay every refutation found by the driver as a checked Isabelle proof.

For each record of class refuted / refuted-at-N1 in results/queries.jsonl, the
recorded Sledgehammer proof is tried first on the narrowest statement the record
supports (the key before migration, if any), then on the record's key. Proofs that
check are written to isabelle/Results_Refutations.thy, which the session
Ground_Map_Checks builds in CI, so nothing counts as refuted unless Isabelle has
checked it. Results go to results/replay.jsonl.
"""
import json, os, re, subprocess, sys, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import driver

ROOT = driver.ROOT
OUT_THY = os.path.join(ROOT, "isabelle", "Results_Refutations.thy")


def stmt(pkg, n1):
    return driver.term(pkg) + (" \\<and> N1" if n1 else "") + " \\<Longrightarrow> False"


BATCH = int(os.environ.get("REPLAY_BATCH", "25"))


def check(cands):
    """cands: list of (name, statement, proof). Returns set of names that check.
    Checked in batches, so that one slow proof costs only its batch; a batch that
    times out as a whole is split and retried down to single lemmas."""
    ok = set()
    for i in range(0, len(cands), BATCH):
        ok |= check_split(cands[i:i + BATCH])
    return ok


def check_split(cands):
    res = check_one(cands)
    if res is None:
        if len(cands) == 1:
            return set()
        h = len(cands) // 2
        return check_split(cands[:h]) | check_split(cands[h:])
    return res


def check_one(cands):
    """One theory; None if the whole run timed out."""
    os.makedirs(driver.WORK, exist_ok=True)
    name = "R_" + hashlib.sha1(repr(cands).encode()).hexdigest()[:10]
    lines = [f"theory {name} imports Ground_Map_Checks.Order Ground_Map_Checks.NonClassical begin"]
    where = {}
    for nm, st, pf in cands:
        lines.append(f'lemma {nm}: "{st}"'); where[len(lines)] = nm
        lines.append("  " + pf); where[len(lines)] = nm
    lines.append("end")
    path = os.path.join(driver.WORK, name + ".thy")
    open(path, "w").write("\n".join(lines) + "\n")
    try:
        p = subprocess.run([driver.ISABELLE, "process_theories", "-O", "-U", "-d", os.path.join(ROOT, "isabelle"),
                            "-l", "Ground_Map_Checks", "-o", "timeout=300", "-f", path, name],
                           capture_output=True, text=True, timeout=600)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", "poly -q"], capture_output=True)
        return None
    if re.search(r"\bTimeout\b", out):
        return None
    # the statement is echoed as "theorem <name>: ..." before its proof runs, so success
    # means: echoed, and no Error reported at the lemma line or its proof line
    bad = set()
    for m in re.finditer(r'Error \(line (\d+) of', out):
        ln = int(m.group(1))
        if ln in where: bad.add(where[ln])
    for m in re.finditer(r'\*\*\* .*?\(line (\d+) of "[^"]*' + name, out):
        ln = int(m.group(1))
        if ln in where: bad.add(where[ln])
    echoed = {nm for nm, _, _ in cands if re.search(r"theorem\s+" + nm + r":", out)}
    return echoed - bad


def main():
    recs = [json.loads(l) for l in open(driver.CACHE)]
    refs = [r for r in recs if r["class"] in ("refuted", "refuted-at-N1") and r.get("proof")]
    cands, meta = [], {}
    for i, r in enumerate(refs):
        n1 = r["class"] == "refuted-at-N1"
        keys = [r.get("key_before_migration"), r["key"]]
        for j, k in enumerate([k for k in keys if k is not None]):
            pkg = k.split(",") if k else []
            nm = f"ref{i}_{j}"
            cands.append((nm, stmt(pkg, n1), r["proof"])); meta[nm] = (r, k, n1)
    # Incremental by default: a record already replayed with the same class keeps its
    # checked key without a new check. That is safe because every replayed lemma is
    # written to Results_Refutations.thy, which the required isabelle check builds.
    # `replay.py --all` checks everything again.
    old = {}
    rp = os.path.join(ROOT, "results", "replay.jsonl")
    if "--all" not in sys.argv and os.path.exists(rp):
        old = {o["key"]: o for o in map(json.loads, open(rp)) if o.get("replayed")}
    kept, todo = set(), []
    for c in cands:
        r, k, n1 = meta[c[0]]
        o = old.get(r["key"])
        if o and o.get("class") == r["class"] and o.get("checked_key") == k:
            kept.add(c[0])
        else:
            todo.append(c)
    todo = [c for c in todo if not any(meta[x][0] is meta[c[0]][0] for x in kept)]
    print(f"{len(kept)} kept from results/replay.jsonl, {len(todo)} statements to check")
    ok = kept | (check(todo) if todo else set())
    best = {}
    for nm in sorted(ok):
        r, k, n1 = meta[nm]
        rid = id(r)
        if rid not in best or len(k) < len(best[rid][1]):
            best[rid] = (nm, k, n1, r)
    with open(os.path.join(ROOT, "results", "replay.jsonl"), "w") as f:
        for r in refs:
            b = best.get(id(r))
            f.write(json.dumps({"key": r["key"], "class": r["class"], "replayed": b is not None,
                                "checked_key": b[1] if b else None}, ensure_ascii=False) + "\n")
    body = ["theory Results_Refutations", "  imports Order NonClassical", "begin", "",
            "text \\<open>Generated by scripts/replay.py from results/queries.jsonl. Each lemma is a",
            "  refutation found by Sledgehammer during the step 4 search, replayed here so that",
            "  Isabelle checks it. Lemmas marked N1 refute the package together with the",
            "  non-triviality floor N1 (class refuted-at-N1); they say nothing about the",
            "  package without N1. Do not edit by hand.\\<close>", ""]
    seen = set()
    for rid, (nm, k, n1, r) in sorted(best.items(), key=lambda x: (len(x[1][1]), x[1][1])):
        if (k, n1) in seen: continue
        seen.add((k, n1))
        pkg = k.split(",") if k else []
        body.append(f"text \\<open>{'refuted at N1 (package and N1)' if n1 else 'refuted'}: {k}\\<close>")
        body.append(f'lemma refuted_{len(seen)}: "{stmt(pkg, n1)}"')
        body.append("  " + r["proof"]); body.append("")
    body.append("end")
    open(OUT_THY, "w").write("\n".join(body) + "\n")
    print(f"{len(best)}/{len(refs)} refutations replayed; {len(seen)} distinct lemmas written to {OUT_THY}")


if __name__ == "__main__":
    main()
