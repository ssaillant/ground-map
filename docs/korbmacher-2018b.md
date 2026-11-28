# Korbmacher 2018b against the registry and finding F9

Report for review, 2026-11-28. Items 1–4 of section 6 were accepted by the reviewer the same day and are implemented in registry 0.8.0-draft (decision D10, findings F20–F23); item 5 is deferred. Sections 1–5 are the report as delivered, except where marked [0.8.0]. Source: Korbmacher, J. (2018). Axiomatic Theories of Partial Ground II: Partial Ground and Hierarchies of Typed Truth. *J Philos Logic* 47: 193–226 (Utrecht repository, publisher version; saved as `sources/Korbmacher-2018b-Axiomatic-theories-partial-ground-II-JPL.pdf`). Journal page = PDF page + 191. The text layer drops the ground symbol ◁; every formula quoted below was read from the page image.

Labels: PAGE = read on the page; CODE = read in the repository, not re-run; INFERENCE = my reasoning, not machine-checked; NOT READ = a source I did not consult. Finding numbers: PR #9 uses F14–F19 and registry 0.7.0-draft, so these are F20 onward in 0.8.0-draft, with decision D10.

---

## 1. What Korbmacher proves

**The puzzle, predicationally (Lemma 1, pp. 198–199, PAGE).** Over PG_T (truth and ground apply to sentences of L_Tr), APT `∀x(Tr(x) → x ◁ Tr(ẋ))` is inconsistent. The derivation is Fine's "something is true": 0=0; Tr(0=0) (T-scheme over L); 0=0 ◁ Tr(0=0) (APT); Tr(Tr(0=0)) (G3, factivity); Tr(0=0) ◁ ∃xTr(x) (U6); Tr(∃xTr(x)) (G3); ∃xTr(x) ◁ Tr(∃xTr(x)) (APT); Tr(Tr(∃xTr(x))) (G3); Tr(∃xTr(x)) ◁ ∃xTr(x) (U6); circle by G2, against G1. For APF he writes "we can perform an analogous derivation, which is left to the interested reader" (p. 199).

**The typed theory (Defs. 1–2, pp. 205–207, PAGE).** Truth predicates Tr_β for 0 < β < ε0, with T3^β `∀x(Tr_β(x) → Sent_<β(x))` (p. 204). Ground is partial ground ◁, irreflexive (G1), transitive (G2), factive per level (G3a/b^β), and its relata are sentences of L_<α (G4^α, "effectively a typing axiom", p. 224). Every axiom of part I (U1–U9 upward, D1–D9 downward, for ¬¬, ∨, ∧, ¬∨, ¬∧, ∃, ∀, ¬∃, ¬∀) holds at every level β. Aristotelian principles hold at every level γ < α:

- APU_T^γ `∀x(Tr_γ(x) → x ◁ Tr_γ(ẋ))`, APU_F^γ `∀x(Tr_γ(¬x) → ¬x ◁ ¬Tr_γ(ẋ))` (p. 207)
- APD_T^β,γ `∀x(Tr_β(Tr_γ(ẋ)) → x ◁ Tr_γ(ẋ))`, APD_F^β,γ `∀x(Tr_β(¬Tr_γ(ẋ)) → ¬x ◁ ¬Tr_γ(ẋ))` (p. 207)

**Results.** PGA_<α proves positive ramified truth PRT_<α (Prop. 1, p. 209); PGA_α is conservative over PRT_α (Thm. 1, p. 212); PGA_<ε0 is consistent (Cor. 3, p. 213); a "standard model" of grounding trees over Tarski's hierarchy (Thm. 2, p. 219). Two levels already suffice: "We could already have stopped at level two … the theory PGA_2 is consistent and proves the following simple version of the typed Aristotelian principle for truth: ∀x(Tr_1(x) → x ◁ Tr_1(ẋ))" (p. 223).

**How the circle is blocked.** "On our approach, the grounds of a truth of the form ∃xTr_α(x) never includes truths of involving a truth predicate Tr_α … in particular, the grounds of the truth of ∃xTr_α(x) don't include the truth of ∃xTr_α(x) itself" (p. 224). Lovett reads it the same way: "∃xT1x < T1⟨∃xT1x⟩ is not an instance of this rule … The closest substitution instance of this rule is ∃xT1x < T2⟨∃xT1x⟩. But T2⟨∃xT1x⟩ is not an instance of ∃xT1x" (Lovett 2020 p. 2551, PAGE).

**Section 4, the "new puzzle" (PAGE).** PUG lets Tr apply to sentences containing ◁ (Def. 8, p. 221). Theorem 3: "Let φ(x) be the formula ¬(x ◁ ¬¬x). By the diagonal lemma … δ ↔ ¬(⌜δ⌝ ◁ ⌜¬¬δ⌝). It is easily checked that we can now both prove δ and ¬δ" (p. 221). The same works with "¬(x ◁ x∨x) or ¬(x ◁ x∧x)" (p. 222). The ground predicate then defines a truth predicate (Prop. 2, p. 222). Footnote 8 (p. 195): "This generalizes some previously results obtained by the author in [13]" (the 2015 Kriterion paper).

**Open problems he names.** A theory of ground with untyped truth "in the spirit of the Kripke-Feferman theory of truth KF … would require the development of new methods and this goes beyond the scope of this paper" (p. 224). A doubly typed theory, with typed ground predicates ◁_1, ◁_2, …: "The results of this paper suggest that this theory will turn out consistent … carrying out the details … is beyond the scope of this paper" (pp. 224–225).

---

## 2. Finding A: F9 is a different solution from Korbmacher's, not a case of it

**What F9 says.** Model MU satisfies W.TR, W.TEM, BETA.ID, CL.PROP, CL.QUANT, **TS.FULL**, TR.TYPED, EX.FULL, ALL.INST, DISJ.ONE, TRANS.P, IRR.F and ASYM.P at N5. MT does the same for the universal argument (audit §12).

**How MU blocks the circle (CODE, `Separation_Models.thy` lines 464–493).** A proposition is a truth value plus a rank. `trT p = (fst p, (1, 0))`: every truth ascription gets rank (1, 0), whatever p's rank. A quantified proposition whose body mentions truth gets rank (1, 3). So for s = "something is true", tr s is true, it is an instance of s, and it lies *below* s. EX.FULL then grounds s in tr s, and TR.TYPED says nothing about s, because s is not truth-free.

**How Korbmacher blocks it.** Tr_1(⌜∃xTr_1(x)⌝) is *false* (T3^1), so it is not a true instance and U6 does not apply. The Aristotelian principle still holds of ∃xTr_1(x), one level up: ∃xTr_1(x) ◁ Tr_2(⌜∃xTr_1(x)⌝).

**A correspondence that makes the comparison exact (INFERENCE, a reading choice).** Read the registry's meta-level T as Korbmacher's union of levels ⋃S_β, its `tr` as Tr_1, and "truth-free" as L_0. Then:

| | Korbmacher PGA_2 | MU / MT |
|---|---|---|
| TS.TYPED (Tr_1's T-scheme on L_0) | holds (Lemma 3 with β = γ = 1) | holds |
| TS.FULL (T(tr p) ↔ T p for all p) | **fails**: T3^1 makes Tr_1 false of every non-L_0 sentence | **holds** |
| TR.TYPED (APU^1) | holds | holds |
| Aristotelian principle above level 1 | holds (APU^γ, through Tr_2, Tr_3, …) | **fails**: no truth entry grounds tr s in s, and tr s grounds s |
| "something is true" grounded in its own truth ascription | **no** (p. 224) | **yes** (`MU_not_TR_PART` and the EX.FULL instance) |
| Ground | partial only | full G {p} |
| Quantifiers | first-order, over codes of sentences | propositional, impredicative, with BETA.ID |
| Grounding for ¬, ∧, and the downward D-axioms | all, at every level | not checked (audit §12, Limits) |

Neither result implies the other. Korbmacher's theory covers more grounding rules. F9 covers full ground, propositional quantification and an untyped truth schema, and it denies what Korbmacher keeps: the Aristotelian principle for semantic truths.

**Literature, so far.** I have not found F9's combination defended: untyped truth schema, impredicative quantification with the truth witness admissible, and Propositional Grounding restricted to truth-free propositions. What I checked:

- Fine sets that option aside. "It is also hard, though perhaps not so hard, to see how we might give up the special assumptions of Factual Grounding, Propositional Grounding, or Truth Introduction. So let us keep these assumptions fixed for the rest of the discussion" (Fine 2010 p. 107, PAGE). Also: "In the case of propositions or sentences, it is hard to see how A might not ground or might not help to ground the truth of the proposition that A" (p. 106).
- Lovett 2020 §6 (pp. 2549–2552, PAGE) surveys Fine, Korbmacher, rejecting irreflexivity, and Woods. None of these is F9's option. His own solution (§7) weakens both T-I and E-I by a weak-ground condition, so that neither strict link holds (p. 2557). In MU the E-I link holds strictly.
- Genco–Poggiolesi–Rossi 2021 only sketch truth (pp. 1446–1447, PAGE). They would keep the Aristotelian rule GrT and add a complexity measure taken from the truth theory, which is Korbmacher's ω-complexity strategy, not F9's.

NOT READ: Krämer 2013 and Donaldson 2016 (Korbmacher fn. 7 says both sketch predicativist solutions); Litland 2015; Correia 2014; Pleitz 2020; Schnieder (forthcoming) "Aristotle's Insight on Truth"; deRosset 2021 "Hollow Truth"; Botticchio 2024, *Type-free Predicational Theories of Ground* (Utrecht MA thesis: a K3/KF-style model of ground and truth, and a predicational version of Fine's puzzle); Korbmacher's 2016 dissertation ch. 2 (pp. 73–106, the same material). So the result is "not found in the sources read", not "undefended".

**What would falsify the novelty claim.** Any of the unread sources restricting the Aristotelian principle to non-semantic propositions while keeping an untyped truth schema.

**A cost and a limit of the F9 strategy (INFERENCE).**

1. In MU, the truth ascription to "something is true" grounds it and is not grounded by it. That reverses the direction that Fine's Aristotle passage and Korbmacher's APU support.
2. Typing TR handles only puzzles that run through `tr`. Correia's operator puzzle (2026 p. 2566, PAGE) puts ∞p := ¬¬p in place of truth. From p ≺ ¬¬p and existential instantiation of ∃p∞p, it gets a violation of Asymmetry with no truth predicate at all. So F9's typing does not block it once λp. ¬¬p is admissible. Korbmacher's approach handles its first-order transcription ∃xTr_1(¬¬x), because there all quantification over truth-bearers goes through a typed truth predicate. This is P.CORREIA.2026, a registry candidate that has not been encoded.

---

## 3. Finding B: the three truth targets do not need TS.FULL

Korbmacher's Lemma 1 gets Tr(Tr(0=0)) from 0=0 ◁ Tr(0=0) by factivity G3, not from a T-scheme (p. 198, steps 3–4, PAGE).

In the registry, `something_true_circle_witness` uses TS_FULL only to get T(tr q) from T q (`Puzzle_Packages.thy` lines 151 and 153, CODE). TR_PART together with the core clause FACT already gives this: PG q (tr q) implies T (tr q). [0.8.0] Now checked: `tr_true_FACT` and the `*_noTS` theorems in `isabelle/Puzzle_Packages.thy` (finding F20). The same step occurs in the universal and particular-props derivations ("T (tr s), so PG (tr s) d").

So the packages of P.FINE.PARTICULAR, P.FINE.UNIVERSAL and P.FINE.PARTICULAR.PROPS are probably not minimal, and TS.FULL can be dropped from all three. This needs Isabelle theorems without TS_FULL before the targets change. It does not affect F9, whose models satisfy TS.FULL anyway.

---

## 4. Finding C: an inconsistency among Korbmacher's stated results

INFERENCE by hand, each step from a printed axiom or lemma. Work in PGA_<3 (levels 1 and 2). Let c = ⌜Tr_1(⌜0=0⌝)⌝, an L_1 sentence that is not in L_0.

1. Tr_2(⌜¬Tr_1(c)⌝) ↔ ¬Tr_1(c). This is Lemma 3 (p. 210: "For all ordinals 0 < γ ≤ β < α < ε0 and for all sentences φ ∈ L_<γ: ⊢PGA<α ∀t1…∀tn(Tr_β(⌜φ(ṫ1,…,ṫn)⌝) ↔ φ(t1,…,tn))"), with φ(x) = ¬Tr_1(x), γ = β = 2, α = 3.
2. ¬Tr_1(c), by T3^1, since PA ⊢ ¬Sent_<1(c). Hence Tr_2(⌜¬Tr_1(c)⌝) by step 1.
3. ⌜¬Tr_1(⌜0=0⌝)⌝ ◁ ⌜¬Tr_1(c)⌝, by APD_F^2,1 at x = ⌜Tr_1(⌜0=0⌝)⌝ (p. 207).
4. Tr_2(⌜¬Tr_1(⌜0=0⌝)⌝), by G3a^2 (p. 205), since Sent_<2(⌜¬Tr_1(⌜0=0⌝)⌝).
5. ¬Tr_1(⌜0=0⌝), by Lemma 3 again. This contradicts T1^1, which gives Tr_1(⌜0=0⌝).

The same Lemma 3 instance together with RP11 (p. 208, printed without restriction as `∀x(Tr_β(¬Tr_γ ẋ) ↔ Tr_γ(¬x))`) gives ∀x(Tr_1(¬x) ↔ ¬Tr_1(x)). That is refuted at x = c by T3^1.

**Diagnosis (INFERENCE).** Lemma 3 holds only for sentences in which truth predicates occur positively, as for positive truth theories generally. Alternatively, APD_F and RP11 need a restriction to Sent_<γ(x) or a disjunct "∨ ¬Sent_<γ(x)", as in KF.

**What survives and what does not.**

- Cor. 3 (consistency) plausibly survives for the printed axioms. PRT as printed has a positive, gappy model, and Thm. 1's translation does not use Lemma 3. This is INFERENCE, not checked.
- Thm. 2 does not survive as stated. In the classical standard model (p. 214), Tr_2(⌜¬Tr_1(c)⌝) is true, but no grounding tree leads from the false ¬Tr_1(⌜0=0⌝) (Lemma 6). So APD_F^2,1 fails there.
- Footnote 24's claim that PRT is "equivalent to … RT" fails for the printed RP11.
- Two small slips: the recursion for S_α+1 on p. 214 is off by one index as printed, and clause (xiv) on p. 217 has #φ where #¬φ is meant.

**What would falsify this.** A published correction, or the dissertation's version (ch. 2, not read) with restricted axioms; then the finding is only about the printed text. Or an error in my reading of Sent_<2 or of the ranges of β and γ.

**Why it matters here.** Lemma 3 is the only verbatim source for TS.TYPED, so it should be cited with this caveat. Any transcription of Korbmacher's theory must decide on APD_F.

---

## 5. Finding D: registry fidelity, all now checked on the page

- **TRANS.P**: korbmacher2018b Def. 1 G2, p. 205. The quote matches.
- **TS.TYPED**: now has a source. Lemma 3, p. 210, quoted above (caveat in Finding C), and T3^β p. 204 `∀x(Tr_β(x) → Sent_<β(x))`. The prose quote under the T₃ reading is on p. 206 and reads "as long as we respect the typing restriction that for all 0 < β ≤ α, if Tr_β(⌜φ⌝), then Sent_<β(⌜φ⌝)". The axiom range is 0 < β < α (pp. 204–205), as the audit had it.
- **TR.TYPED**: APU_T^γ on p. 207; the quote matches up to the underdot. The two-level reading now has explicit support from p. 223 (quoted in §1). The full-versus-partial flag stands: ◁ is partial ground (p. 193).
- **TR.NEG**: APU_F^γ on p. 207; the quote matches. The source is typed, and the entry is untyped (already flagged).
- **Correspondence flag (new).** Under the correspondence in §2, TS.FULL contradicts Korbmacher's T3^1. The registry's TS chain (TS.TYPED below TS.FULL) therefore has no entry for his position. See proposal 2 below.
- **P.KORBMACHER.2015**: add 2018b Thm. 3 (p. 221) as the published source of `korbmacher_dn`, whose diagonal formula matches exactly, and p. 222 for the ∨ and ∧ variants. Encoding note: what 2018b isolates as the cause is letting Tr apply to ◁-sentences (T3◁, T1◁, T2◁, p. 221). In the registry that step is built into the signature, because T is a HOL predicate on every proposition and PG is a HOL relation, so the only hypothesis left is DIAG.K. Korbmacher's three responses (p. 224) are "typed", "untyped" (restricting the ground principles) and "non-classical". They map onto three registry routes: denying DIAG.K, the DISJ.GRD repair (F13), and the strong Kleene model K1 (F11).
- **F11 literature line**: "Korbmacher 2018b … (web copy, partly read)" is now read. P. 224 names KF-style untyped truth with ground as beyond its scope. Botticchio 2024 appears to build such a model, which is a lead to read before F11's position is called new.
- **korbmacher2018b bibliography entry**: read = publisher version (Utrecht repository), read in full; page offset +191; `needed_from_reviewer: false`.

---

## 6. Proposed registry changes

[0.8.0] Status: 1–4 implemented (see the notes after each); 5 deferred; 6 unchanged.

1. **Restate F9's novelty and limits paragraph** with the comparison in §2. [0.8.0] Done: F9's consequence, finding F23, and the novelty fields of the MT and MU records.
2. **New entry TS.T3** (Korbmacher's T3 at two levels): `tfree a = False ∧ fv a = {} ⟶ ¬ T (tr (den v a))`. **New consistency target P.KORBMACHER.2018B.TYPED**, expected modelled: W.TR, W.TEM, BETA.ID, CL.PROP, CL.QUANT, TS.TYPED, TS.T3, TR.TYPED, EX.FULL, ALL.INST, DISJ.ONE, NEG.DN, CONJ.BIN, TRANS.P, IRR.F. This transcribes Korbmacher's own solution as far as one `tr` allows. Korbmacher's theorem does not cover it (full ground, propositional quantifiers), so it needs its own model.
   - Reading choice: TS.T3 forces propositions to be fine-grained. No truth-free sentence may denote the same true proposition as a sentence that mentions truth, so coarse models are excluded.
   - TS.T3 sits outside the TS chain, because it contradicts TS.FULL.
   - [0.8.0] Done. `TS_T3` in `isabelle/Principles.thy`; `TS_T3_not_FULL` and `TS_T3_grain` check the incompatibility and the grain. Model MK (`isabelle/Korbmacher_Typed.thy`, `MK_package`) satisfies the package, with ASYM.P added, at N5 (finding F22). Cost found in MK: with s the universal closure of f_tem, neg (tr s) partially grounds s (`MK_neg_tr_grounds`), which Fine's (*) p. 104 rejects; INFERENCE, not checked, that Korbmacher's standard model shares it.
3. **New entry NEG.ALL** (Korbmacher U9, p. 205: `∀x∀t∀v(Tr_β(¬x(t/v)) → ¬x(t/v) ◁ ¬∀vx)`; Fine 2012a's ¬∀ rule to be checked). **New target P.KORBMACHER.APF**, the falsity version that Korbmacher left to the reader. My reconstruction is "not everything is true". s = all f_tr is false; by TR.NEG, ¬s ◁ ¬tr s; ¬tr s is a true negated instance of s, so ¬tr s ◁ ¬s by NEG.ALL; the circle violates IRR.F. Package: W.TR, BETA.ID, CL.PROP, CL.QUANT, TS.FULL, TR.NEG, NEG.ALL, TRANS.P, IRR.F. Expected refuted, flagged as a reconstruction. It tests whether F9 extends to the falsity clause, which would need the typed TR.NEG that the registry lists as a v1.1 candidate. [0.8.0] Done. `NEG_ALL` in `isabelle/Principles.thy`; `korbmacher_apf_W` refutes the package without using FACT (finding F21).
4. **Finding B**: Isabelle theorems without TS_FULL, then drop TS.FULL from the three truth targets. [0.8.0] Done (finding F20).
5. **Finding C** [deferred by the reviewer]: record it with an abstract Isabelle lemma of the five-step derivation (a schematic check that the cited axioms are jointly inconsistent, not a formalization of PGA). Claim nothing about Cor. 3.
6. **Leave as candidates** (out of scope for v1): the full hierarchy (needs an indexed `tr`), the doubly typed theory (needs an indexed ground; it is Korbmacher's conjecture, pp. 224–225), and P.CORREIA.2026 as the scope test of F9.

Tooling note: sections 1–5 were written without running Isabelle. The 0.8.0 theorems were built locally with the pinned Isabelle2026 (session Ground_Map_Checks) and are checked by the PR's CI.

---

## Addendum, 2026-11-28: Krämer 2013, Donaldson (draft), Litland 2015

The reviewer supplied three sources that §2 listed as unread. They are now in `sources/`: `Kramer-2013-A-simpler-puzzle-of-ground-Thought-eprint.pdf` (Glasgow eprint, accepted manuscript, no journal pagination), `Donaldson-Metaphysical-Foundations-of-Arithmetic-draft.pdf` (draft, 36 pp., draft pagination), `Litland-2015-Grounding-explanation-limit-of-internality-PhilRev.pdf` (journal pages 481–532). Labels as above.

### A1. What they say about F9's option (PAGE)

- **Krämer 2013** lists rejecting the Aristotelian principle as a known response to the Finean version and credits it to Skiles: "Skiles (ms.) advocates rejecting (A) as well as my assumption (i) from the beginning of the paper" (fn. 6). His point is that this does not reach his own puzzle: "Since none of the other auxiliary assumptions (PE), (TI), (A), and (TG) are used in my argument, rejecting any of these will not by itself help with the latter." F9 agrees: W.ID refutes the typed package (`kramer_W`). His own predicativist option restricts (EG-S) "to cases in which α is free of sentential quantifiers", or uses "a hierarchy of sentential quantifiers". That is EX.PRED and EX.LEV, not a restriction of (A).
- **Donaldson** (appendix, pp. 25–27) has a second-order analogue of Fine's universal argument. His λ rule is "If ⟨λx: φ(x)⟩t, then [⟨λx : φ(x)⟩t]←[φ(t)]" (p. 25), and his instance is ⟨λx : ∀X(Xx ∨ ¬Xx)⟩a (p. 26). Predication-grounding plays the part that truth-grounding plays for Fine. His "neo-Russellian" solution restricts which properties exist: "⟨λ0x: ∃X1 X1x⟩" does not represent a property (p. 27). He identifies it with Fine's predicativist approach: "I think that when Fine (2010) mentions a 'predicativist' approach to his puzzles, he has something like my neo-Russellian proposal in mind" (endnote xlii, p. 36). That is a restriction of comprehension, which F9 does not make.
- **Litland 2015 §6.3** (pp. 493–494) is the nearest option found. As a contextualist response, he considers restricting Truth-grounding by type: "φ ≺ T⌜φ⌝ holds only when the truth-property assigned to 'T' is of a 'higher' type than any truth-property assigned to a truth-predicate occurring in φ" (p. 493). He objects that "the contextualist needs to independently motivate the restriction on Truth-grounding", since his scenarios are not paradoxical (p. 494). He then keeps truth untyped.
  - F9 differs from that option in two ways. It has one untyped truth predicate and an untyped truth schema. Its restriction is also stronger: the truth ascription to a proposition that is not truth-free is never grounded in that proposition, at any level.
  - INFERENCE: Litland's motivation objection applies to F9 with more force than to the contextualist.

**Effect on the novelty claim.** Giving up (A) is a known response (Skiles, via Krämer). Typed Truth-grounding is a considered response (Litland, Korbmacher). What remains for F9 is specific: (A) restricted to truth-free propositions, together with an untyped truth schema and impredicative quantification, with a machine-checked model. Skiles's manuscript is now the closest unread lead.

### A2. A caveat on F20 found while reading Krämer (CODE, checked)

Krämer's (A) reads "If <p> is true then p ≺ <p> is true", and he needs Truth-Introduction (TI) to reach (F2). Fine's Propositional Grounding (p. 101) and Korbmacher's APT (p. 198) also take the truth of the truth ascription as antecedent. The registry's TR.PART instead has antecedent T p. That reading was already flagged on the entry ("under TS.FULL the two coincide"). With FACT, it entails truth introduction (`TR_PART_TI`), and that is why TS.FULL could be dropped.

With the sources' antecedent, the three truth targets are not refuted without TS.FULL. Model MK satisfies that form of the principle for every proposition, together with every other entry of the three targets, and fails TS.FULL (`MK_TR_A`, `MK_truth_targets_source_form` in `isabelle/Korbmacher_Typed.thy`).

So F20 is restated as follows: TS.FULL is redundant given the registry's TR.PART, which does the work of truth introduction. Litland's Truth-grounding (p. 488, Figure 1, "φ / φ ≺ T⌜φ⌝", partial strict ground) has the registry's antecedent. It is added as a source for TR.PART.

### A3. P.KRAMER checked against the source (PAGE)

The package and derivation match (1)–(2):
- "∃p p" is "a theorem of any standard logic with sentential quantification".
- "(1) is a true instance of itself", by the null context of (EG-S).
- Footnote 4 says the claims "are standardly taken to hold for both partial and complete grounding", so EX.FULL is supported as well as EX.PART.

One locator was corrected (ASYM.P: "paragraph after (F3)/(F4)", not "introduction"). The registry writes "<" for Krämer's "≺".

### A4. Litland 2015 and the registry

- **Internality argument** (pp. 487–491). It is modal ("it is necessary that if f and c both obtain, then f grounds c", p. 481), and it needs contingent self-reference through labels. The v1 signature has no worlds, and the proposed family SR has only fixed self-referential propositions. So no target is proposed for v1. Its non-modal step has the structure of Fine's fn. 15, which Litland cites (p. 488) and the registry checks (`fine_fn15`, F12). The reading is recorded on the candidate P.LITLAND.INTERNALITY.
- **F11.** Appendix B (pp. 522–532) gives models of strict full immediate ground for Kripke's theory of truth. It covers strong Kleene and supervaluation, with untyped truth and first-order quantifiers in a free logic. Ground comes from spanning forests built in stages (§8.5, pp. 516–517). That is prior art for Kripkean ground with untyped truth.
  - K1 differs in three ways: it has propositional quantifiers, beta identity and a fixed domain.
  - It also defines ground by efficient premises rather than by deleting inferences.
  - INFERENCE: neither construction is a special case of the other. F11's literature note now says this.

### A5. Proposals

[D11] The reviewer accepted 1 and 2 the same day; both are implemented in registry 0.8.0-draft (entry TR.PART.A, target P.DONALDSON.SP, finding F24). For 3, the reviewer will look for Skiles's manuscript.

1. **Target P.DONALDSON.SP (cheap).** This is a propositional transcription of Donaldson's puzzle: the sentence-position universal argument with BETA.GROUND in place of BETA.ID, i.e. [W.EM, BETA.GROUND, CL.PROP, CL.QUANT, ALL.PART, DISJ.PART, TRANS.P, IRR.F]. Expected refuted, by this derivation:
   - s = all f_em.
   - app f_em s ≺ s by ALL.PART.
   - disj s (neg s) fully grounds app f_em s by BETA.GROUND.
   - s ≺ disj s (neg s) by DISJ.PART.
   - Transitivity then gives PG s s.

   It records that where predication grounds, as for Donaldson, the circle closes without any truth predicate, so typing TR (F9) does not help. It is a reconstruction, because Donaldson's quantifier ranges over properties of individuals, which the signature lacks.
2. **Entry TR.PART.A** (the Aristotelian principle with the sources' antecedent, now `TR_PART_A` in Korbmacher_Typed.thy). Making it an entry would turn the F20 caveat into a result about registry packages. The cost is one more entry in the TR family.
3. **Sources to request:** Skiles (ms.), "Some solutions to some puzzles of ground" (Krämer fn. 6; the closest lead for F9's novelty), and Botticchio 2024 (for F11).
