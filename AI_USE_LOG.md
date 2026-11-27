# AI-use log

Record of prompts and model versions used to produce this repository, for the
AI-use disclosure. One entry per working session.

## 2026-11-26 — Step 1: registry draft (principles/registry.yaml v0.1.0-draft)

- Tool: Claude Code (cloud session), project thread "Build the Ground Map registry".
- Model: claude-opus-5-5 (configured model id; the serving model was not independently confirmed).
  Source retrieval used web-fetch subagents running in the same session.
- Prompt: the user's build brief of 2026-11-26 (steps 1–6, rules, definition of
  done), with the decisions: v1 primitive is strict full factive mediate ground;
  sets in Isabelle, bounded-size ground predicates (≤ 3 grounds) in the
  first-order mirror; empty and infinitary grounds as registry entries; stop for
  review after step 1.
- What the model did: searched for open-access copies of the sources; extracted
  verbatim formulations by automated text extraction (Woods 2018 published PDF;
  Krämer 2013 accepted manuscript; Korbmacher 2018 I/II and Correia 2014
  repository copies); drafted families, formal statements and reading choices.
- What the model could not access: Fine 2010, Fine 2012a, Fine 2012b, Fritz 2022
  (abstract only), deRosset & Fine 2023. Entries citing them are marked
  `unverified` or `secondary`.
- Human review: pending (step 1 review stop).

## 2026-11-26 — Decision note, machine checks, source verification (registry v0.1.1-draft)

- Tool: Claude Code (cloud session), same project thread. Model: claude-opus-5-5
  (configured id; serving model not independently confirmed). Source retrieval
  for Kment, Goodman and Fritz 2023 used web-fetch subagents.
- Prompts: (1) the user's request for fuller context on registry decisions 1–3
  and for a proof check and literature check of X.RUSSELL.ALL; (2) "here are
  the requested PDFs", relayed with the instruction to verify quotations and
  page references in the registry and the decision note and update the
  verification tags.
- What the model did: wrote the decision note (Claude Doc "Ground Map: registry
  decisions, explained"); installed Isabelle2026 (tarball SHA-256
  858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d) after the
  user's environment allowed isabelle.in.tum.de and dists.isabelle.cit.tum.de;
  wrote and built isabelle/Russell_Checks.thy (session Ground_Map_Checks; no
  sorry, oops or axioms); extracted text from the user's PDFs (Fritz 2022
  published, with a hidden text layer from another article filtered out by font;
  Fine 2012b published; Fine 2012a author manuscript; deRosset & Fine 2023
  preprint; Fine & deRosset 2024 x2; deRosset 2015) and checked quotations and
  pages against them; revised registry to 0.1.1-draft and the decision note.
- Not available: Fine 2010; Lovett 2019; Krämer 2013 journal pages; CUP pages of
  Fine 2012a. deRosset & Fine 2023 not yet mined.
- Human review: pending (decisions 1–3 open).

## 2026-11-26 — Fine 2010 and Lovett verification (registry v0.1.2-draft)

- Tool and model as above (claude-opus-5-5 configured).
- Prompt: reviewer accepted manuscript pagination for Fine 2012a; then supplied
  Fine 2010 and Lovett 2020 with "Here you go", relayed with the instruction to
  verify the entries citing them and update their tags.
- What the model did: extracted text (Lovett's rule schemas read from a page
  image); re-tagged every fine2010 citation as published-page; corrected the
  DISJ.BOTH attribution; added DISJ.WEAK, EX.WEAK and witness f_tem; split the
  Fine universal target; wrote isabelle/Fine_Checks.thy (4 theorems, no
  sorry/oops/axioms, builds in Isabelle2026); updated the decision note.
- Not yet mined: Fine 2010 sect. 8; Lovett sects. 7–8 (weak ground, outside v1).

## 2026-11-26 — Reviewer decisions D1–D3 implemented (registry v0.2.0-draft)

- Tool and model as above (claude-opus-5-5 configured).
- Prompt: "Implement recommendations" (reviewer), relayed as approval of the
  decision-note recommendations for decisions 1–3, to be implemented and recorded
  with date and version.
- What the model did: designed the formula layer (datatype fm, den, lam, fv, subf,
  lvl, tfree), adm-based comprehension (C1, C2, C3d, C3s), BETA family, defined
  immediate ground IG/IPG (Fritz p. 322) with IMM.CONJ, and Woods vacuity vacW;
  wrote isabelle/Signature.thy (no sorry/oops/axioms) with kramer_v2,
  kramer_vacuous, grain_from_conj_imm, fritz_cantor_imm, fritz_p315_imm; restated
  the affected registry entries; recorded D1–D3 in registry section `decisions`.
- Reading choices made by the model, flagged in the registry: the clause
  "G Γ q" in IG; vacW's choice of presentation and its one-world test; C2 bound
  k = 1; BETA.GROUND with distinctness.
- Human review: decisions approved; the encodings themselves await review.

## 2026-11-27 — Fritz main result; step 3 validation (registry v0.2.1-draft)

- Tool and model as above (claude-opus-5-5 configured).
- Prompt: "Proceed" (reviewer), after the report proposing Fritz's seven
  principles and then step 3. The CUP volume of Correia & Schnieder (2012) was
  supplied in another thread and used for Fine 2012a page numbers.
- What the model did: wrote isabelle/Fritz_Main.thy (Fritz §2.4 for any factive
  relation and for IPG), isabelle/No_Finite_Models.thy (finding F1), added
  fine_universal_sp; added IMM.FRITZ7; recorded step 3 as passed; moved Guide
  citations to CUP pages. All theories build in Isabelle2026, no sorry/oops/axioms.
- Human review: step 3 review stop (per the brief).

## 2026-11-27 — Decision D4 (infinite-model class)

- Tool and model as above.
- Prompt: reviewer chose "Add an infinite-model class" on a decision card that
  presented finding F1 (no finite models for CL.PROP + TRANS.P + IRR.F with any of
  CONJ.BIN, DISJ.ONE, TR.FULL).
- What the model did: recorded D4 in principles/registry.yaml (classes refuted,
  finite-model, infinite-model, unknown; infinite-model certified by a model built
  in Isabelle, e.g. a term model) and marked F1 as decided. No proofs changed.
- Human review: decision made by the reviewer; certificate construction not yet done.

## 2026-11-27 — Repository scaffold

- Tool and model as above.
- Prompt: "Go ahead and create the GitHub repository" (reviewer).
- What the model did: wrote README.md, TOOLS.md (pinned Isabelle2026 + sha256),
  LICENSE (BSD-3-Clause, the model's choice, matching the AFP's licence; awaiting
  reviewer confirmation), scripts/check_no_sorry.sh, a GitHub Actions workflow that
  verifies the pinned tarball, checks for sorry/oops/axiomatization and builds the
  session, and empty results/ and docs/. The session could not create the GitHub
  repository itself (API refused), so the reviewer creates it and the model pushes.
- Human review: pending.

## 2026-11-27 — Push to GitHub; Korbmacher's puzzle

- Tool and model as above.
- Prompts: "Approve", "Let's go" (reviewer; read as go-ahead for step 4), plus
  Korbmacher's 2015 slides.
- What the model did: pushed the history to ssaillant/ground-map (repo created by
  the reviewer); wrote isabelle/Korbmacher_Checks.thy (diagonal witness as an
  explicit hypothesis; disjunction and double-negation versions; untyped
  response); registry entries for the new sources and candidate puzzles. Builds in
  Isabelle2026, no sorry/oops/axioms.
- Human review: pending.

## 2026-11-27 — Step 4 groundwork: encoding, order, driver, model verifier

- Tool and model as above.
- Prompt: "Let's go" (reviewer).
- What the model did: isabelle/Principles.thy (all registry entries as constants),
  isabelle/Order.thy (proved implications used for propagation), scripts/driver.py
  (Sledgehammer/Nitpick batches via process_theories; classes refuted, finite-model,
  trivial-only, unknown; cache results/queries.jsonl), scripts/verify_models.py
  (second, Python implementation of the semantics that re-checks each Nitpick
  model; tested to reject corrupted models). CI fixed to use the https mirror.
- Human review: pending.

## 2026-11-27 — Fritz 2020 checked; five new sources

- Tool and model as above.
- Prompt: reviewer upload of Goodman 2023, Genco–Poggiolesi–Rossi 2021, Krämer & Roski
  2015, Poggiolesi 2022, Fritz "On higher-order logical grounds".
- What the model did: read Fritz in full; wrote isabelle/Fritz2020_Checks.thy (the
  beta-grounding cases: against asymmetry, and with transitivity against
  irreflexivity); registry target P.FRITZ2020.BETAG and bibliography entries.
  Builds, no sorry/oops/axioms. The other four papers were only identified.
- Human review: pending.

## 2026-11-27 — Propagation fix; refutation replay; results page; README for philosophers

- Tool and model as above.
- Prompt: reviewer's questions about legibility and novelty (relayed by the coordinator).
- What the model did: found and fixed unsound propagation into formula-layer
  entries (records migrated conservatively: refutation keys widened, models kept);
  stopped the third cloud growth run; scripts/replay.py (20/20 refutations replay,
  isabelle/Results_Refutations.thy, built in CI); verifier parsing fixes (111/111
  models verified; corruption test fails as it should); scripts/summarize.py
  generating docs/results.md, checked in CI; README rewritten for philosophers.
- Human review: pending.

## 2026-11-27 — Isabelle model certificates for the 12 principles unknown on their own

- Tool and model as above (Claude Code, cloud session; Isabelle2026 pinned, hash checked).
- Prompt: "Maybe the one I can do now?" then "Proceed" and "Approve" (reviewer), relayed by
  the coordinator as: classify the registry principles that were unknown when tested alone.
- What the model did: found 12 (the 11 listed on the results page plus IRR.W, never
  queried alone); wrote isabelle/Model_Certificates.thy (locale gsig with the signature's
  constants as parameters, faithfulness lemmas K_* against Signature/Principles, five
  models MA-ME with N1-N5 evidence, theorem imm_fritz7_no_finite_model); records in
  results/isabelle_models.jsonl; summarize.py section 4; registry finding F2; README.
  Session builds, no sorry/oops/axioms.
- Reading choices made by the model and flagged for review: N3 counted as vacuous when a
  package selects no introduction entry; N4 stated with an explicit witness pair; Isabelle-
  built models with finite carriers classed as finite-model although scripts/verify_models.py
  cannot re-check them (it does not implement the formula layer).
- Human review: pending.

## 2026-11-27 — Infinite-model certificate M1 (decision D4)

- Tool and model as above (Claude Code, cloud session; Isabelle2026 pinned, hash checked).
- Prompt: "Looking good, now infinite models" (reviewer).
- What the model did: wrote isabelle/Models.thy. The principles are restated over a record
  of operations (gstr) and lemma `fidelity` proves that at the actual constants each
  restatement is the definition in Principles.thy. Term model M1: propositions are closed
  terms, application is a constructor of its own, ground is the least relation closed
  under the package's introduction principles, cut and amalgamation. Theorem M1_package
  certifies a 20-entry classical package with N1, N2, N5 (finding F3); M1 refutes BETA.ID
  and BETA.GROUND. Lemma neg_as_function_refutes mechanizes Goodman 2023's negation variant
  of Krämer's puzzle (finding F4). Record in results/isabelle_models.jsonl; summarize.py
  lists Isabelle-built packages and checked non-candidates. Literature check against
  Fritz 2020 (read in full earlier) and Goodman 2023 sections 1-2 (PDF pp. 4-10): the
  consistency result is not new (Goodman 2023 sec. 2, appendices A-B).
- Reading choices made by the model and flagged for review: dependence uses Fine-style
  polarity clauses (negated conjunctions depend on negated conjuncts); the metatheoretic
  step from the restated principles to the uninterpreted constants is stated in text,
  not checked; whether M1 is a sub-case of Goodman's appendix A models is an inference
  not yet checked (his section 2 negation yields mere truth conditions, so NEG.DN fails
  there).
- Human review: pending.


## 2026-11-27 — Non-classical families: strong Kleene, Korbmacher's untyped repair, Poggiolesi

- Tool and model as above (Claude Code, cloud session; Isabelle2026 pinned, hash checked).
- Prompt: "yes" (reviewer), to the coordinator's proposal to add the non-classical families -
  (a) Korbmacher-style grounding restricted to grounded truths, (b) a Kripke-style
  fixed-point truth predicate, (c) Poggiolesi's finer-negation repair of Wilhelm.
- What the model did: read korbmacher2015 (slides), fine2010 sect. 8 and notes 12-15,
  poggiolesi2022 in full, Goodman 2023 sect. 4; web checks of Litland 2022, Korbmacher
  2018b, Schindler 2014 and the PhilArchive citations of Wilhelm 2021 (via fetch, summary
  level). Wrote isabelle/Poggiolesi_Checks.thy (Wilhelm's inconsistency; Poggiolesi's
  published interpretation fails her condition (1); a normal-form model proves her
  theorem), isabelle/NonClassical.thy (strong Kleene definitions and order lemmas; liar
  results; Fine p. 109 reproduced; DISJ.ONE refuted under SK twice; Korbmacher's untyped
  repair plus foundation refuted) and isabelle/Kripke_Model.thy (strong Kleene term model
  K1 with Kripke stages and efficient ground; certifies Fine's compromise package with
  BETA.ID and C3d at N1, N2, N5). Registry section `proposed` (0.3.0-draft, pending
  review), candidates P.WILHELM.2021 and P.POGGIOLESI.2022, findings F5-F8. Session builds,
  no sorry/oops/axioms.
- Reading choices made by the model and flagged for review: T stays bivalent at the
  metalevel (gaps are propositions with neither T p nor T (neg p)); Fine's existence
  predicate and putative domain omitted; bigconj a gap in K1; strict efficiency, not
  fn. 13's broadened notion; SR.LIAR as identity; DIAG.K non-atomic; Fund read as atomic and
  Korbmacher's slide-3 formula taken as a principle he does not assert; Poggiolesi's ≅ read
  literally, ≐ as any relation containing it, Leibniz's law as a congruence reading.
- Not entered in the enumeration (driver.py) or results/ until the reviewer adopts the
  entries.
- Human review: pending.
