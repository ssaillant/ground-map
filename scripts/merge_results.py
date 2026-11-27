#!/usr/bin/env python3
"""Merge per-job results (artifacts) into results/queries.jsonl and results/grow.jsonl,
keeping one record per package key (a definite class beats unknown)."""
import glob, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RANK = {"refuted": 3, "finite-model": 3, "trivial-only": 2, "unknown": 0}
parts = sys.argv[1] if len(sys.argv) > 1 else "parts"
best = {}
for f in [os.path.join(ROOT, "results", "queries.jsonl")] + glob.glob(os.path.join(parts, "*", "queries.jsonl")):
    if not os.path.exists(f): continue
    for line in open(f):
        r = json.loads(line)
        k = r["key"]
        if k not in best or RANK.get(r["class"], 0) > RANK.get(best[k]["class"], 0):
            best[k] = r
with open(os.path.join(ROOT, "results", "queries.jsonl"), "w") as out:
    for r in best.values():
        out.write(json.dumps(r, ensure_ascii=False) + "\n")
grows = set()
for f in [os.path.join(ROOT, "results", "grow.jsonl")] + glob.glob(os.path.join(parts, "*", "grow.jsonl")):
    if os.path.exists(f):
        grows.update(open(f).read().splitlines())
with open(os.path.join(ROOT, "results", "grow.jsonl"), "w") as out:
    out.write("\n".join(sorted(g for g in grows if g.strip())) + "\n")
print(len(best), "package records;", len(grows), "grow runs")
