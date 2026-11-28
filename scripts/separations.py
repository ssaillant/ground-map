#!/usr/bin/env python3
"""Separating models for rank pairs of the registry (section implications).

For a pair (HI, LO) of entries where the registry ranks HI above LO and Order.thy
proves no implication, this script asks Nitpick for a finite model of

    FACT and HI and N1 and not LO

A genuine model shows that HI does not imply LO, with at least one grounding fact. The
model is then re-checked by the independent implementation of the semantics in
verify_models.py. Records go to results/separations.jsonl; summarize.py re-checks each
stored model every time it renders the results page, so CI re-verifies them without
Isabelle.

Only pairs outside the formula layer are tried: there Nitpick's models are genuine.
Usage: separations.py            (needs the session heap; ISABELLE as for driver.py)
       separations.py --check    (re-check the stored models only)
"""
import hashlib, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import driver
import verify_models as vm

ROOT = driver.ROOT
OUT = os.path.join(ROOT, "results", "separations.jsonl")

# (holds, fails): the higher-ranked entry and the lower-ranked one it does not include
PAIRS = [("CL.QUANT", "CL.PROP"), ("ID.DN", "ID.AC"), ("CONJ.INF", "CONJ.BIN"),
         ("CONJ.GRAIN", "CONJ.BIN"), ("DISJ.BOTH", "DISJ.ONE"), ("NEG.DM", "NEG.DN"),
         ("TR.NEG", "TR.FULL")]


def check(rec):
    """Re-check a stored model: FACT, the entry in `holds` and N1 true, the entry in `fails` false."""
    card, consts = vm.parse_model(rec["model"])
    M = vm.Model(card, consts)
    try:
        vals = {e: vm.ev(M, e) for e in ["FACT", "N1", rec["holds"], rec["fails"]]}
    except KeyError as ex:
        return {"verified": None, "reason": f"not checkable: {ex}"}
    ok = vals["FACT"] and vals["N1"] and vals[rec["holds"]] and not vals[rec["fails"]]
    return {"verified": bool(ok), "values": vals, "card": card}


def run(t_np=30):
    os.makedirs(driver.WORK, exist_ok=True)
    name = "S_" + hashlib.sha1(repr(PAIRS).encode()).hexdigest()[:10]
    lines = [f"theory {name} imports Ground_Map_Checks.Order begin"]
    where = {}
    for i, (hi, lo) in enumerate(PAIRS):
        lines.append(f'lemma s{i}: "\\<not> (FACT \\<and> {driver.ENTRIES[hi]} \\<and> N1 \\<and> \\<not> {driver.ENTRIES[lo]})"')
        lines.append("  " + driver.NP.format(t=t_np)); where[len(lines)] = i
        lines.append("  oops")
    lines.append("end")
    path = os.path.join(driver.WORK, name + ".thy")
    open(path, "w").write("\n".join(lines) + "\n")
    out = subprocess.run([driver.ISABELLE, "process_theories", "-O", "-U", "-d", os.path.join(ROOT, "isabelle"),
                          "-l", "Ground_Map_Checks", "-f", path, name],
                         capture_output=True, text=True, timeout=120 + 2 * t_np * len(PAIRS)).stdout
    recs = []
    for m in re.finditer(r'Output \(line (\d+) of "[^"]*"\):\n(.*?)(?=\nOutput \(line |\nFinished |\Z)', out, re.S):
        ln, body = int(m.group(1)), m.group(2)
        if ln in where and "Nitpick found a counterexample" in body and "potentially spurious" not in body:
            hi, lo = PAIRS[where[ln]]
            recs.append({"holds": hi, "fails": lo, "with": ["FACT", "N1"], "model": body.strip(),
                         "source": "nitpick", "registry": "0.3.1-draft"})
    return recs


if __name__ == "__main__":
    if "--check" in sys.argv:
        recs = [json.loads(l) for l in open(OUT)]
    else:
        recs = run()
        with open(OUT, "w") as f:
            for r in recs:
                f.write(json.dumps(r, ensure_ascii=False) + "\n")
    found = {(r["holds"], r["fails"]) for r in recs}
    for r in recs:
        c = check(r)
        print(f'{r["holds"]:11} does not imply {r["fails"]:9} verified={c["verified"]} card={c.get("card")}')
    for p in PAIRS:
        if p not in found:
            print(f"{p[0]:11} / {p[1]:9} no genuine model found")
    sys.exit(0 if all(check(r)["verified"] for r in recs) else 1)
