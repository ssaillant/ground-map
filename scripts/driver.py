#!/usr/bin/env python3
"""Step 4 driver: MARCO-style exploration of the principle lattice.

A package is a set of registry entries. Every query runs in Isabelle2026 against
the session Ground_Map_Checks (heap must be built: isabelle build -b -D isabelle).
For each package P the driver asks, in one batch theory:

  refute:   P ==> False                      (Sledgehammer)
  model:    not (P and N1)                   (Nitpick; a genuine counterexample is a model)
  refuteN1: P and N1 ==> False               (Sledgehammer; "trivial only")

Classification of a single query:
  refuted        Sledgehammer proof of P ==> False (replayed later as a checked proof)
  trivial-only   no model with N1 found and P and N1 refuted
  finite-model   Nitpick reports a genuine model of P and N1
  unknown        anything else, including every timeout. Never "consistent".

Propagation uses only the unconditional implications proved in isabelle/Order.thy:
a refutation of P refutes every Q whose closure contains P's closure, and a model
of Q is a model of every P whose closure is contained in Q's.
"""
import itertools, json, os, random, re, subprocess, sys, time, hashlib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ISABELLE = os.environ.get("ISABELLE", "/opt/Isabelle2026/bin/isabelle")
WORK = os.environ.get("GM_WORK", "/tmp/claude-0/gm-driver")
CACHE = os.path.join(ROOT, "results", "queries.jsonl")

# registry id -> Isabelle term (isabelle/Principles.thy, Signature.thy)
ENTRIES = {
    "IRR.W": "IRR_W", "IRR.F": "IRR_F", "IRR.MEM": "IRR_MEM",
    "ASYM.ANTI": "ASYM_ANTI", "ASYM.P": "ASYM_P",
    "TRANS.P": "TRANS_P", "TRANS.CUT": "TRANS_CUT",
    "AMALG.FIN": "AMALG_FIN", "AMALG.INF": "AMALG_INF",
    "CL.PROP": "CL_PROP", "CL.QUANT": "CL_QUANT",
    "TS.TYPED": "TS_TYPED", "TS.FULL": "TS_FULL", "TS.ID": "TS_ID",
    "ID.AC": "ID_AC", "ID.DN": "ID_DN",
    "CONJ.BIN": "CONJ_BIN", "CONJ.INF": "CONJ_INF", "CONJ.GRAIN": "CONJ_GRAIN",
    "DISJ.ONE": "DISJ_ONE", "DISJ.BOTH": "DISJ_BOTH", "DISJ.WEAK": "DISJ_WEAK",
    "NEG.DN": "NEG_DN", "NEG.DM": "NEG_DM",
    "EX.PRED": "EX_PRED", "EX.LEV": "EX_LEV", "EX.FULL": "EX_FULL", "EX.WEAK": "EX_WEAK",
    "ALL.INST": "ALL_INST", "ALL.TOT": "ALL_TOT",
    "TR.TYPED": "TR_TYPED", "TR.FULL": "TR_FULL", "TR.NEG": "TR_NEG",
    "EMPTY.NONE": "EMPTY_NONE", "EMPTY.SOME": "EMPTY_SOME",
    "FIN.FIN": "FIN_FIN", "FIN.B3": "FIN_B3",
    "C1": "C1", "C2": "(C2 1)", "C3d": "C3d", "C3s": "C3s",
    "BETA.ID": "BETA_ID", "BETA.GROUND": "BETA_GROUND",
    "IMM.CONJ": "IMM_CONJ", "IMM.FRITZ7": "IMM_FRITZ7",
}
# unconditional implications proved in Order.thy (stronger, weaker)
IMPL = [("IRR.F", "IRR.W"), ("IRR.F", "IRR.MEM"), ("ASYM.P", "ASYM.ANTI"),
        ("TRANS.CUT", "TRANS.P"), ("AMALG.INF", "AMALG.FIN"),
        ("TS.ID", "TS.FULL"), ("TS.FULL", "TS.TYPED"), ("TR.FULL", "TR.TYPED"),
        ("EX.FULL", "EX.LEV"), ("EX.FULL", "EX.PRED"), ("FIN.B3", "FIN.FIN")]
# at most one entry from each group (exact characterisations of adm, or contradictory)
EXCL = [{"C1", "C2", "C3d", "C3s"}, {"EMPTY.NONE", "EMPTY.SOME"}, {"BETA.ID", "BETA.GROUND"}]
# entries that mention lam/den: the core clause LAM_CORE is added when one is present
LAMB = {"IRR.W", "TS.TYPED", "TR.TYPED", "EX.PRED", "EX.LEV", "C1", "C2", "C3d",
        "BETA.ID", "BETA.GROUND"}

SH = 'sledgehammer [timeout = {t}, provers = "vampire e cvc5 z3 zipperposition", minimize = false, preplay_timeout = 5]'
NP = 'nitpick [timeout = {t}, card prp = 1-6, card pfun = 1-3, max_threads = 1, show_consts, format = 1]'


def closure(pkg):
    s = set(pkg)
    changed = True
    while changed:
        changed = False
        for a, b in IMPL:
            if a in s and b not in s:
                s.add(b); changed = True
    return frozenset(s)


def admissible(pkg):
    return all(len(set(pkg) & g) <= 1 for g in EXCL)


def reduce(pkg):
    """Drop entries implied by others (canonical generator of the closure)."""
    c = closure(pkg)
    return frozenset(e for e in c if not any(a in c and b == e for a, b in IMPL))


def term(pkg):
    parts = ["FACT"] + (["LAM_CORE"] if set(pkg) & LAMB else []) + sorted(ENTRIES[e] for e in pkg)
    return " \\<and> ".join(parts)


def key(pkg):
    return ",".join(sorted(reduce(pkg)))


class Store:
    def __init__(self):
        self.res = {}
        if os.path.exists(CACHE):
            for line in open(CACHE):
                r = json.loads(line); self.res[r["key"]] = r

    def add(self, r):
        self.res[r["key"]] = r
        os.makedirs(os.path.dirname(CACHE), exist_ok=True)
        with open(CACHE, "a") as f:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")

    def refuted(self):
        return [closure(r["key"].split(",") if r["key"] else []) for r in self.res.values()
                if r["class"] in ("refuted",)]

    def models(self):
        return [closure(r["key"].split(",") if r["key"] else []) for r in self.res.values()
                if r["class"] == "finite-model"]

    def known(self, pkg):
        c = closure(pkg)
        for r in self.refuted():
            if r <= c: return "refuted"
        for m in self.models():
            if c <= m: return "finite-model"
        k = key(pkg)
        if k in self.res: return self.res[k]["class"]
        return None


def run_batch(pkgs, t_sh=20, t_np=20):
    os.makedirs(WORK, exist_ok=True)
    name = "Q_" + hashlib.sha1("|".join(key(p) for p in pkgs).encode()).hexdigest()[:10]
    lines = [f"theory {name} imports Ground_Map_Checks.Order begin"]
    where = {}
    for i, p in enumerate(pkgs):
        tm = term(p)
        lines.append(f'lemma r{i}: "{tm} \\<Longrightarrow> False"'); where[len(lines)] = (i, "refute")
        lines[-1] += ""; lines.append("  " + SH.format(t=t_sh)); where[len(lines)] = (i, "refute"); lines.append("  oops")
        lines.append(f'lemma m{i}: "\\<not> ({tm} \\<and> N1)"')
        lines.append("  " + NP.format(t=t_np)); where[len(lines)] = (i, "model"); lines.append("  oops")
        lines.append(f'lemma n{i}: "{tm} \\<and> N1 \\<Longrightarrow> False"')
        lines.append("  " + SH.format(t=t_sh)); where[len(lines)] = (i, "refuteN1"); lines.append("  oops")
    lines.append("end")
    path = os.path.join(WORK, name + ".thy")
    open(path, "w").write("\n".join(lines) + "\n")
    t0 = time.time()
    try:
        out = subprocess.run([ISABELLE, "process_theories", "-O", "-U", "-d", os.path.join(ROOT, "isabelle"),
                              "-l", "Ground_Map_Checks", "-f", path, name],
                             capture_output=True, text=True, timeout=120 + 3 * (t_sh + t_np) * max(1, len(pkgs) // 4)).stdout
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
    finally:
        subprocess.run(["pkill", "-f", "poly -q"], capture_output=True)
    elapsed = time.time() - t0
    # split messages by "Output (line N of"
    msgs = {}
    for m in re.finditer(r'Output \(line (\d+) of "[^"]*"\):\n(.*?)(?=\nOutput \(line |\nFinished |\Z)', out, re.S):
        msgs.setdefault(int(m.group(1)), []).append(m.group(2))
    results = []
    for i, p in enumerate(pkgs):
        info = {"refute": None, "model": None, "refuteN1": None, "model_text": None}
        for ln, (j, kind) in where.items():
            if j != i: continue
            for body in msgs.get(ln, []):
                if kind in ("refute", "refuteN1"):
                    m = re.search(r"Try this:\s*(by .*?)\s*\(\d+(?:\.\d+)? m?s\)", body, re.S)
                    if m and info[kind] is None:
                        info[kind] = " ".join(m.group(1).split())
                elif kind == "model":
                    if re.search(r"Nitpick found a counterexample", body) and "potentially spurious" not in body:
                        info["model"] = "genuine"; info["model_text"] = body.strip()
                    elif "potentially spurious" in body and info["model"] is None:
                        info["model"] = "spurious?"
        if info["refute"]:
            cls = "refuted"
        elif info["model"] == "genuine":
            cls = "finite-model"
        elif info["refuteN1"]:
            cls = "trivial-only"
        else:
            cls = "unknown"
        results.append({"key": key(p), "class": cls, "proof": info["refute"] or info["refuteN1"],
                        "model": info["model_text"], "nitpick": info["model"], "batch": name,
                        "t_sh": t_sh, "t_np": t_np, "date": time.strftime("%Y-%m-%d")})
    return results, elapsed


def evaluate(store, pkgs, batch=6, **kw):
    todo = []
    for p in pkgs:
        if not admissible(p): continue
        if store.known(p) is None and key(p) not in {key(q) for q in todo}:
            todo.append(p)
    for i in range(0, len(todo), batch):
        res, el = run_batch(todo[i:i + batch], **kw)
        for r in res:
            store.add(r)
            print(f"  [{r['class']:12}] {r['key'] or '(core)'}", flush=True)
        print(f"  batch of {len(res)} in {el:.0f}s", flush=True)


def shrink(store, pkg):
    """Deletion-based shrink of a refuted package to a minimal refuted one."""
    cur = set(reduce(pkg))
    for e in sorted(cur):
        cand = cur - {e}
        evaluate(store, [cand])
        if store.known(cand) == "refuted":
            cur = cand
    return frozenset(cur)


def grow(store, order, width=6, **kw):
    """Greedy growth along `order`. Candidates cur+e are tested `width` at a time in
    one batch; the first one (in order) with a model is accepted. Refuted candidates
    are shrunk to minimal refuted packages; unknown candidates are skipped."""
    cur, rest = set(), list(order)
    while rest:
        cands = [e for e in rest if admissible(cur | {e})]
        if not cands: break
        evaluate(store, [cur | {e} for e in cands[:width]], batch=width, **kw)
        accepted = None
        for e in cands[:width]:
            st = store.known(cur | {e})
            if st == "finite-model" and accepted is None:
                accepted = e
            elif st == "refuted":
                shrink(store, cur | {e})
        done = cands[:width] if accepted is None else cands[:cands.index(accepted) + 1]
        rest = [e for e in rest if e not in done and e in cands]
        if accepted is not None:
            cur.add(accepted)
    return cur


if __name__ == "__main__":
    store = Store()
    mode = sys.argv[1] if len(sys.argv) > 1 else "singletons"
    if mode == "singletons":
        evaluate(store, [[]] + [[e] for e in ENTRIES])
    elif mode == "pairs":
        evaluate(store, [list(c) for c in itertools.combinations(ENTRIES, 2)])
    elif mode == "pkg":
        evaluate(store, [sys.argv[2].split(",")])
    elif mode == "grow":
        seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        order = list(ENTRIES); random.Random(seed).shuffle(order)
        m = grow(store, order)
        print("maximal consistent (in this order):", ",".join(sorted(m)), flush=True)
        os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
        with open(os.path.join(ROOT, "results", "grow.jsonl"), "a") as f:
            f.write(json.dumps({"seed": seed, "order": order, "maximal": sorted(m),
                                "date": time.strftime("%Y-%m-%d")}) + "\n")
