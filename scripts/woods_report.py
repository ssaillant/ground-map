#!/usr/bin/env python3
"""Classify every target of results/targets/woods-fine.json and write
results/woods_search.jsonl (one record per target), which scripts/summarize.py prints.

A target is
  model     if a model built in Isabelle (results/isabelle_models.jsonl) satisfies it:
            every entry of the target follows, by the implications proved in
            isabelle/Order.thy, from the entries the model's record lists (key and
            also_holds, each proved for the model in Isabelle);
  refuted   if Isabelle has checked a proof - a theorem named in HAND below, or a
            Sledgehammer proof from the search that scripts/replay.py has replayed;
  unknown   otherwise. A Sledgehammer proof that was not replayed counts as unknown.
A target that came out both modelled and refuted would be a contradiction; the script
stops if that happens.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import driver

ROOT = driver.ROOT
# Refutations proved by hand in Isabelle: (entries, theorem). A target is refuted by one
# if the target implies every entry listed.
HAND = [
    (["W.ID", "BETA.ID", "CL.QUANT", "EX.PART", "IRR.F"], "kramer_W (Puzzle_Packages.thy)"),
    (["W.TR", "BETA.ID", "CL.QUANT", "TS.FULL", "EX.PART", "TR.PART", "TRANS.P", "IRR.F"],
     "something_true_trans_W (Puzzle_Packages.thy)"),
    (["W.TR", "BETA.ID", "CL.QUANT", "TS.FULL", "EX.PART", "TR.PART", "ASYM.P"],
     "something_true_asym_W (Puzzle_Packages.thy)"),
    (["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "ALL.PART", "DISJ.PART", "TR.PART", "TRANS.P", "IRR.F"],
     "fine_universal_W (Puzzle_Packages.thy)"),
    (["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.PART", "DISJ.PART", "TR.PART", "TRANS.P", "IRR.F"],
     "fine_particular_props_W (Puzzle_Packages.thy)"),
    (["W.EM", "BETA.ID", "CL.PROP", "CL.QUANT", "ALL.PART", "DISJ.PART", "TRANS.P", "IRR.F"],
     "fine_universal_sp_W (Puzzle_Packages.thy)"),
    (["C2", "BETA.ID", "CL.PROP", "CL.QUANT", "EX.PART", "DISJ.PART", "TRANS.P", "IRR.F"],
     "woods_obj3_refuted (Woods_Models.thy)"),
    (["W.ID", "BETA.ID", "CL.QUANT", "EX.PART", "ASYM.P"], "kramer_W_asym (Woods_Models.thy)"),
    (["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "ALL.PART", "DISJ.PART", "TR.PART", "TRANS.P", "ASYM.P"],
     "fine_universal_W_asym (Woods_Models.thy)"),
    (["W.TEM", "BETA.ID", "CL.PROP", "CL.QUANT", "TS.FULL", "EX.PART", "DISJ.PART", "TR.PART", "TRANS.P", "ASYM.P"],
     "fine_particular_props_W_asym (Woods_Models.thy)"),
    (["W.EM", "BETA.ID", "CL.PROP", "CL.QUANT", "ALL.PART", "DISJ.PART", "TRANS.P", "ASYM.P"],
     "fine_universal_sp_W_asym (Woods_Models.thy)"),
    (["C2", "BETA.ID", "CL.PROP", "CL.QUANT", "EX.PART", "DISJ.PART", "TRANS.P", "ASYM.P"],
     "woods_obj3_asym (Woods_Models.thy)"),
]


# Order in which a fitting model is named: the model of all five targets first, then its
# readings at lower comprehension levels, then the models built for one added entry.
ORDER = ["MV", "MV1", "MV2", "MV3", "MY", "MY2", "MZ", "MZ2", "MQ", "MQ2", "MX", "MX2", "MW"]


def full_closure(pkg):
    """Closure under every implication proved in Order.thy (driver.PROVED). Used only to
    compare a target with a model or a theorem whose own statement includes LAM_CORE."""
    s = set(pkg)
    changed = True
    while changed:
        changed = False
        for a, b in driver.PROVED:
            if a in s and b not in s:
                s.add(b); changed = True
    return s


def load(p):
    p = os.path.join(ROOT, p)
    return [json.loads(l) for l in open(p) if l.strip()] if os.path.exists(p) else []


def main():
    spec = json.load(open(os.path.join(ROOT, "results", "targets", "woods-fine.json")))
    queries = {r["key"]: r for r in load("results/queries.jsonl")}
    replay = {r["key"]: r for r in load("results/replay.jsonl")}
    certs = [c for c in load("results/isabelle_models.jsonl") if c.get("lam_core")]
    out = []
    for t in spec["targets"]:
        pkg = t["package"]
        cl = full_closure(pkg)
        rec = {"id": t["id"], "base": t["base"], "kind": t["kind"], "added": t["added"],
               "key": ",".join(sorted(pkg))}
        models = []
        for c in certs:
            holds = full_closure(c["key"].split(",") + c.get("also_holds", []))
            if set(pkg) <= holds:
                models.append(c)
        hand = [thm for ents, thm in HAND if set(ents) <= cl]
        q = queries.get(driver.key(pkg))
        rp = replay.get(driver.key(pkg), {})
        searched = None
        if q is not None:
            searched = q["class"]
            rec["search"] = {"class": q["class"], "proof": q.get("proof"), "nitpick": q.get("nitpick"),
                             "t_sh": q.get("t_sh"), "replayed": bool(rp.get("replayed"))}
        else:
            rec["search"] = None
        refuted_by = hand[0] if hand else None
        if not refuted_by and searched == "refuted" and rp.get("replayed"):
            refuted_by = "search, replayed in isabelle/Results_Refutations.thy"
        if models and refuted_by:
            sys.exit(f"CONTRADICTION: {t['id']} has model {models[0]['model']} and refutation {refuted_by}")
        if models:
            # name the first fitting model in the order of ORDER; the others are listed
            # (a model may have two records, with different entries and levels: the
            # record with the higher level is used where both fit)
            m = min(models, key=lambda c: (ORDER.index(c["model"]) if c["model"] in ORDER else len(ORDER),
                                           -int(c["nontriviality"][1])))
            rec["other_models"] = sorted({c["model"] for c in models} - {m["model"]})
            rec.update({"class": m["class"], "model": m["model"], "nontriviality": m["nontriviality"].split(" ")[0],
                        "certificate": m.get("certificate")})
        elif refuted_by:
            rec.update({"class": "refuted", "theorem": refuted_by})
        else:
            rec["class"] = "unknown"
            if searched == "refuted":
                rec["note"] = "Sledgehammer reported a proof that was not replayed; not counted"
            elif searched == "refuted-at-N1":
                rec["note"] = "search: refuted together with N1 (" + ("replayed" if rp.get("replayed") else "not replayed") + ")"
        out.append(rec)
    with open(os.path.join(ROOT, "results", "woods_search.jsonl"), "w") as f:
        for r in out:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    from collections import Counter
    print(Counter(r["class"] for r in out))
    for r in out:
        if r["class"] == "unknown":
            print("  unknown:", r["id"])


if __name__ == "__main__":
    main()
