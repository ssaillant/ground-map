#!/usr/bin/env python3
"""Independent re-verification of Nitpick models (step 4).

Nitpick's printed model (with show_consts) is parsed and every principle of the
package, plus FACT and N1, is evaluated by a second implementation of the
semantics written here in Python, separately from the Isabelle definitions in
isabelle/Principles.thy. A model counts as verified only if every conjunct
evaluates to True. Entries of the formula layer (lam/den) are not implemented;
packages containing them are reported as "not checkable".

Usage: verify_models.py [results/queries.jsonl]  -> writes results/models_verified.jsonl
"""
import itertools, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------- parser
class P:
    def __init__(self, s):
        self.s, self.i = s, 0

    def ws(self):
        while self.i < len(self.s) and self.s[self.i] in " \n\t": self.i += 1

    def peek(self, t):
        self.ws(); return self.s.startswith(t, self.i)

    def eat(self, t):
        self.ws()
        if not self.s.startswith(t, self.i):
            raise ValueError(f"expected {t!r} at {self.s[self.i:self.i+40]!r}")
        self.i += len(t)

    def term(self):
        self.ws()
        if self.peek("(λx. _)"):
            self.eat("(λx. _)")
            d = {}
            if self.peek("("):
                self.eat("(")
                while True:
                    k = self.term(); self.eat(":="); v = self.term(); d[k] = v
                    if self.peek(","): self.eat(","); continue
                    self.eat(")"); break
            return ("fun", tuple(sorted(d.items(), key=repr)))
        if self.peek("{"):
            self.eat("{"); xs = []
            if not self.peek("}"):
                while True:
                    xs.append(self.term())
                    if self.peek(","): self.eat(","); continue
                    break
            self.eat("}"); return frozenset(xs)
        if self.peek("("):
            self.eat("("); t = self.term(); self.eat(")"); return t
        m = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:⇩\d+)?").match(self.s, self.i)
        if not m: raise ValueError(f"cannot parse at {self.s[self.i:self.i+40]!r}")
        self.i = m.end(); w = m.group(0)
        if w == "True": return True
        if w == "False": return False
        return w


def as_fun(t):
    if isinstance(t, tuple) and t and t[0] == "fun":
        return {k: as_fun(v) for k, v in t[1]}
    return t


def parse_model(text):
    card = {}
    for m in re.finditer(r"card (\w+) = (\d+)", text.split("\n")[0]):
        card[m.group(1)] = int(m.group(2))
    consts = {}
    sec = text.split("Constants:", 1)
    if len(sec) == 2:
        # one "name = term" per logical line; continuation lines are indented deeper
        body = sec[1]
        for m in re.finditer(r"^\s{4}(\S+) = (.*?)(?=^\s{4}\S+ = |\Z)", body, re.S | re.M):
            consts[m.group(1).split(".")[-1]] = as_fun(P(m.group(2)).term())
    return card, consts


# ---------------------------------------------------------------- semantics
class Model:
    def __init__(self, card, c):
        k = card.get("prp", 1)
        self.D = [f"p⇩{i}" for i in range(1, k + 1)]
        self.c = c
        self.subsets = [frozenset(s) for r in range(len(self.D) + 1) for s in itertools.combinations(self.D, r)]
        pf = card.get("pfun", 1)
        self.F = [f"f⇩{i}" for i in range(1, pf + 1)]
        if "app" in c:
            self.F = sorted(c["app"].keys(), key=str)

    def f(self, name, *args):
        v = self.c[name]
        for a in args:
            v = v[a]
        return v

    def has(self, name): return name in self.c
    def T(self, p): return self.f("T", p)
    def G(self, S, p): return self.f("G", frozenset(S), p)
    def PG(self, p, q): return any(p in S and self.G(S, q) for S in self.subsets)
    def IG(self, S, q):
        return self.G(S, q) and all(not self.G(Dl, q) or all(any(self.G(Dp, p) for Dp in self.subsets if Dp <= Dl) for p in S - Dl) for Dl in self.subsets)
    def IPG(self, p, q): return any(p in S and self.IG(S, q) for S in self.subsets)
    def app(self, f, p): return self.f("app", f, p)
    def sat(self, f): return frozenset(p for p in self.D if self.T(self.app(f, p)))
    def inst(self, f): return frozenset(self.app(f, p) for p in self.D)
    def adm(self, f): return self.f("adm", f) if self.has("adm") else True


def ev(M, e):
    D, S, F = M.D, M.subsets, M.F
    A = lambda: [(p, q) for p in D for q in D]
    neg = lambda p: M.f("neg", p); conj = lambda p, q: M.f("conj", p, q)
    disj = lambda p, q: M.f("disj", p, q); tr = lambda p: M.f("tr", p)
    if e == "FACT": return all(not M.G(G, p) or (M.T(p) and all(M.T(q) for q in G)) for G in S for p in D)
    if e == "N1": return any(M.G(G, p) for G in S for p in D)
    if e == "IRR.F": return all(not M.G(G, c) or c not in G for G in S for c in D)
    if e == "IRR.MEM":
        vac = lambda G, a, c: a in G and all(not M.T(b) or M.G((G - {a}) | {b}, c) for b in D)
        return all(not (M.G(G, c) and c in G) or vac(G, c, c) for G in S for c in D)
    if e == "ASYM.ANTI": return all(not (M.PG(p, q) and M.PG(q, p)) or p == q for p, q in A())
    if e == "ASYM.P": return all(not M.PG(p, q) or not M.PG(q, p) for p, q in A())
    if e == "TRANS.P": return all(not (M.PG(p, q) and M.PG(q, r)) or M.PG(p, r) for p in D for q in D for r in D)
    if e == "TRANS.CUT":
        for G in S:
            for q in D:
                if not M.G(G, q): continue
                for Dl in S:
                    if not Dl <= G: continue
                    choices = [[H for H in S if M.G(H, p)] for p in sorted(Dl)]
                    for Hs in itertools.product(*choices):
                        U = (G - Dl).union(*Hs) if Hs else G - Dl
                        if not M.G(U, q): return False
        return True
    if e == "AMALG.FIN": return all(not (M.G(G, p) and M.G(H, p)) or M.G(G | H, p) for G in S for H in S for p in D)
    if e == "AMALG.INF":
        for p in D:
            Gs = [G for G in S if M.G(G, p)]
            for r in range(1, len(Gs) + 1):
                for fam in itertools.combinations(Gs, r):
                    if not M.G(frozenset().union(*fam), p): return False
        return True
    if e == "CL.PROP":
        return all((M.T(neg(p)) == (not M.T(p))) and (M.T(conj(p, q)) == (M.T(p) and M.T(q)))
                   and (M.T(disj(p, q)) == (M.T(p) or M.T(q))) for p, q in A())
    if e == "CL.QUANT":
        return all((M.T(M.f("exq", f)) == any(M.T(M.app(f, a)) for a in D))
                   and (M.T(M.f("allq", f)) == all(M.T(M.app(f, a)) for a in D))
                   and (M.T(M.f("bigconj", f)) == all(M.T(q) for q in M.sat(f))) for f in F)
    if e == "TS.FULL": return all(M.T(tr(p)) == M.T(p) for p in D)
    if e == "TS.ID": return all(tr(p) == p for p in D)
    if e == "ID.AC":
        return all(conj(p, q) == conj(q, p) and disj(p, q) == disj(q, p) and conj(p, conj(q, r)) == conj(conj(p, q), r)
                   and disj(p, disj(q, r)) == disj(disj(p, q), r) and conj(p, p) == p and disj(p, p) == p
                   for p in D for q in D for r in D)
    if e == "ID.DN": return all(neg(neg(p)) == p for p in D)
    if e == "CONJ.BIN": return all(not (M.T(p) and M.T(q)) or M.G({p, q}, conj(p, q)) for p, q in A())
    if e == "CONJ.INF":
        return all(not (M.adm(f) and M.sat(f) and all(M.T(q) for q in M.sat(f))) or M.G(M.sat(f), M.f("bigconj", f)) for f in F)
    if e == "CONJ.GRAIN":
        a = all(not (M.T(conj(p, q)) and conj(p, q) == conj(p2, q2)) or {p, q} == {p2, q2}
                for p in D for q in D for p2 in D for q2 in D)
        b = all(not (M.adm(f) and M.adm(g) and all(M.T(q) for q in M.sat(f)) and all(M.T(q) for q in M.sat(g))
                     and M.f("bigconj", f) == M.f("bigconj", g)) or M.sat(f) == M.sat(g) for f in F for g in F)
        return a and b
    if e == "DISJ.ONE": return all((not M.T(p) or M.G({p}, disj(p, q))) and (not M.T(q) or M.G({q}, disj(p, q))) for p, q in A())
    if e == "DISJ.BOTH": return all(not (M.T(p) and M.T(q)) or M.G({p, q}, disj(p, q)) for p, q in A())
    if e == "DISJ.WEAK": return all(not M.T(disj(p, q)) or M.PG(p, disj(p, q)) or M.PG(q, disj(p, q)) for p, q in A())
    if e == "NEG.DN": return all(not M.T(p) or M.G({p}, neg(neg(p))) for p in D)
    if e == "NEG.DM":
        return all((not M.T(neg(p)) or M.G({neg(p)}, neg(conj(p, q)))) and (not M.T(neg(q)) or M.G({neg(q)}, neg(conj(p, q))))
                   and (not (M.T(neg(p)) and M.T(neg(q))) or M.G({neg(p), neg(q)}, neg(disj(p, q)))) for p, q in A())
    if e == "EX.FULL": return all(not (M.adm(f) and M.T(M.app(f, a))) or M.G({M.app(f, a)}, M.f("exq", f)) for f in F for a in D)
    if e == "EX.WEAK": return all(not (M.adm(f) and M.T(M.f("exq", f))) or any(M.PG(M.app(f, a), M.f("exq", f)) for a in D) for f in F)
    if e == "ALL.INST": return all(not (M.adm(f) and all(M.T(M.app(f, a)) for a in D)) or M.G(M.inst(f), M.f("allq", f)) for f in F)
    if e == "ALL.TOT":
        return all(not (M.adm(f) and all(M.T(M.app(f, a)) for a in D))
                   or (M.T(M.f("tot", f)) and M.G(M.inst(f) | {M.f("tot", f)}, M.f("allq", f))) for f in F)
    if e == "TR.FULL": return all(not M.T(p) or M.G({p}, tr(p)) for p in D)
    if e == "TR.NEG": return all(not M.T(neg(p)) or M.G({neg(p)}, neg(tr(p))) for p in D)
    if e == "EMPTY.NONE": return all(not M.G(frozenset(), p) for p in D)
    if e == "EMPTY.SOME": return any(M.G(frozenset(), p) for p in D)
    if e == "FIN.FIN": return True  # every set over a finite domain is finite
    if e == "FIN.B3": return all(not M.G(G, p) or len(G) <= 3 for G in S for p in D)
    if e == "C3s":
        allfun = itertools.product(D, repeat=len(D))
        tables = {tuple(M.app(f, p) for p in D) for f in F}
        return all(M.adm(f) for f in F) and all(h in tables for h in allfun)
    if e == "IMM.CONJ":
        return all(not (M.adm(f) and all(M.T(r) for r in M.sat(f)))
                   or all(M.IPG(p, M.f("bigconj", f)) == (p in M.sat(f)) for p in D) for f in F)
    raise KeyError(e)


def verify(rec):
    pkg = rec["key"].split(",") if rec["key"] else []
    card, consts = parse_model(rec["model"])
    M = Model(card, consts)
    out = {}
    for e in ["FACT", "N1"] + pkg:
        try:
            out[e] = ev(M, e)
        except KeyError as ex:
            return {"key": rec["key"], "verified": None, "reason": f"not checkable: {ex} not implemented or constant not printed"}
    ok = all(out.values())
    return {"key": rec["key"], "verified": ok, "failed": [e for e, v in out.items() if not v], "card": card}


if __name__ == "__main__":
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "results", "queries.jsonl")
    recs = {}
    for line in open(src):
        r = json.loads(line)
        if r["class"] == "finite-model" and r.get("model") and "Constants:" in r["model"]:
            recs[r["key"]] = r
    res = [verify(r) for r in recs.values()]
    with open(os.path.join(ROOT, "results", "models_verified.jsonl"), "w") as f:
        for v in res:
            f.write(json.dumps(v, ensure_ascii=False) + "\n")
    n = len(res); ok = sum(1 for v in res if v["verified"]); bad = [v for v in res if v["verified"] is False]
    print(f"{ok}/{n} models verified; {len(bad)} failed; {n - ok - len(bad)} not checkable")
    for v in bad + [v for v in res if v["verified"] is None]:
        print(" ", v)
