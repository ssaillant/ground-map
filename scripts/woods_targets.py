#!/usr/bin/env python3
"""Write results/targets/woods-fine.json: the search set for Woods's substantive
irreflexivity (IRR.W) in place of strict irreflexivity (IRR.F).

Bases. The five Krämer and Fine targets of the registry (puzzles.targets) with IRR.W
for IRR.F; the package of Woods's Objection 3 (woods2018 p. 643, the existential
of p ∨ A, which needs a propositional function outside the four witnesses, hence C2);
and the union of the five.

For each base the set contains
  - the base itself,
  - controls: IRR.F in place of IRR.W (the published puzzle; expected refuted),
    IRR.MEM in place of IRR.W (the membership reading, a control entry), and ASYM.P
    added (expected refuted: the packages force a truth that helps ground itself),
  - one package for each registry entry in EXT added to the base.
Two further packages: the union at full strength (full-ground entries, TRANS.CUT) and
the package that model MV of isabelle/Woods_Models.thy satisfies; a refutation of
either would contradict that model.

The driver classifies each package as refuted or unknown. It cannot return a model
here: every package mentions the formula layer (IRR.W, the witness entries, BETA.ID),
where Nitpick reports only potentially spurious models.
"""
import json, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BASES = {
    "P.KRAMER/W": ["W.ID", "BETA.ID", "CL.QUANT", "EX.PART", "IRR.W"],
    "P.FINE.PARTICULAR/W": ["W.TR", "BETA.ID", "CL.QUANT", "TS.FULL", "TR.PART", "EX.PART", "TRANS.P", "IRR.W"],
    "P.FINE.UNIVERSAL/W": ["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "ALL.PART", "DISJ.PART",
                           "TR.PART", "TRANS.P", "IRR.W"],
    "P.FINE.PARTICULAR.PROPS/W": ["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.PART", "DISJ.PART",
                                  "TR.PART", "TRANS.P", "IRR.W"],
    "P.FINE.UNIVERSAL.SP/W": ["W.EM", "BETA.ID", "CL.PROP", "CL.QUANT", "ALL.PART", "DISJ.PART", "TRANS.P", "IRR.W"],
    "P.WOODS.OBJ3": ["C2", "BETA.ID", "CL.PROP", "CL.QUANT", "EX.PART", "DISJ.PART", "TRANS.P", "IRR.W"],
    "P.UNION/W": ["W.ID", "W.TR", "W.EM", "W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.PART",
                  "ALL.PART", "DISJ.PART", "TR.PART", "TRANS.P", "IRR.W"],
}
EXT = ["ASYM.ANTI", "TRANS.CUT", "AMALG.FIN", "AMALG.INF", "TS.ID", "TS.KF", "ID.AC", "ID.DN",
       "CONJ.BIN", "CONJ.INF", "DISJ.ONE", "DISJ.BOTH", "NEG.DN", "NEG.DM", "EX.FULL", "ALL.INST",
       "ALL.TOT", "TR.FULL", "TR.NEG", "EMPTY.NONE", "EMPTY.SOME", "FIN.FIN", "FIN.B3",
       "C1", "C2", "C3d", "C3s", "IMM.CONJ", "IMM.FRITZ7"]
COMP = {"C1", "C2", "C3d", "C3s"}
FULL = ["W.ID", "W.TR", "W.EM", "W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.FULL", "ALL.INST",
        "DISJ.ONE", "TR.FULL", "TRANS.CUT", "IRR.W"]
MV = ["C3s", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.FULL", "ALL.INST", "CONJ.INF", "CONJ.BIN",
      "DISJ.ONE", "DISJ.BOTH", "TR.FULL", "TR.NEG", "NEG.DN", "NEG.DM", "TRANS.CUT", "AMALG.INF",
      "EMPTY.NONE", "IRR.W"]

targets = []
def add(tid, base, kind, pkg, added=None):
    targets.append({"id": tid, "base": base, "kind": kind, "added": added, "package": sorted(set(pkg))})

for b, pkg in BASES.items():
    add(b, b, "base", pkg)
    add(b + " with IRR.F", b, "control", [e for e in pkg if e != "IRR.W"] + ["IRR.F"], "IRR.F for IRR.W")
    add(b + " with IRR.MEM", b, "control", [e for e in pkg if e != "IRR.W"] + ["IRR.MEM"], "IRR.MEM for IRR.W")
    add(b + " + ASYM.P", b, "control", pkg + ["ASYM.P"], "ASYM.P")
    for e in EXT:
        if e in pkg or (e in COMP and COMP & set(pkg)):
            continue
        add(b + " + " + e, b, "extension", pkg + [e], e)
add("P.UNION/W at full strength", "P.UNION/W", "model-check", FULL)
add("package of model MV", "P.UNION/W", "model-check", MV)

out = os.path.join(ROOT, "results", "targets", "woods-fine.json")
json.dump({"name": "woods-fine", "t_sh": 45, "t_np": 15, "targets": targets}, open(out, "w"), indent=1, ensure_ascii=False)
print(len(targets), "targets ->", out)
