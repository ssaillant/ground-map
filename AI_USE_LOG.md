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

## 2026-11-27 — Independent faithfulness audit; second opinion on the certificate rules

- Tool: Claude Code (cloud session), project thread "Review formalizations against the
  sources"; Isabelle2026 pinned, hash checked. Source retrieval for works not in the
  project files (Krämer 2013, Woods 2018, Korbmacher 2018a/b, Correia 2014) used
  web-fetch subagents in the same session, which return verbatim fragments of at most
  125 characters.
- Model: a different model from the entries above, at the reviewer's request. Its
  identifier is recorded in the project thread and is to be entered here by the reviewer.
- Prompt: "let's open up a thread to read the sources again but with [the model named by
  the reviewer] and do/review 1 and 2" (reviewer), where 1 is the faithfulness of the
  formalizations and 2 the four certificate rules; with the coordinator's note asking for
  a per-entry verdict table that separates textual evidence, verification and inference,
  and for clear citation errors only to be fixed.
- What the model did: re-read every cited passage it could reach (page images for Fine
  2012b, Fritz 2022 and Lovett's rule display); compared each registry statement with
  Principles.thy and each puzzle proof with the published derivation; wrote
  docs/audit-2026-11-27.md and isabelle/Audit_Checks.thy; corrected five citation errors
  in the registry (listed in the report, section 7). No statement and no status label was
  changed.
- Main results, all for review: four restricted entries are provably equivalent to their
  unrestricted counterparts in the current encoding; the registry's chain convention is
  not what Principles.thy implements; "trivial-only" is assigned without a model; Fine's
  partial Universal Grounding has no entry; Fine's Cut was misquoted from an OCR layer.
- Human review: pending.

## 2026-11-27 — Repairs after the audit (registry 0.3.0-draft)

- Tool: Claude Code (cloud session), the same project thread as the audit; Isabelle2026
  pinned. Sources were read from the project files (page images where the text layer is
  unreliable); nothing was re-fetched for the repair.
- Model: the same model as the audit entry above; identifier to be entered by the
  reviewer.
- Prompt: "Please repair all" (reviewer), in reply to the audit report. Read as: carry
  out the repairs proposed under findings A1 to A4 and the report's list "Proposed and
  not done".
- What the model did: changed the four restricted entries to closed formulas in
  Principles.thy and in the certificate locale; built the model MG
  (isabelle/Restricted_Models.thy); added four partial-ground entries and proved the
  Krämer and Fine targets from the registry constants (isabelle/Puzzle_Packages.thy);
  renamed the search class trivial-only to refuted-at-N1 and recomputed 22 search rows;
  rewrote the registry's convention on chains, added its `implications` section,
  decision D5, findings F5 and F6, source additions and flagged readings; regenerated
  docs/results.md; added section 10 to the audit report.
- Decisions the model took itself, listed in the registry under D5
  (`choices_made_in_applying_it`) and in the report, section 10: C2 left unchanged;
  EX.LEV closes the instance only; three partial entries beyond the one the audit named;
  CL.PROP added to one puzzle target.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/replay.py (20 of 20
  refutations replayed); scripts/verify_models.py (113 of 113 models, two at level N0).
- Human review: pending.

## 2026-11-27 — Open questions of the repair (registry 0.3.1-draft)

- Tool: Claude Code (cloud session), the same project thread as the audit; Isabelle2026
  pinned. No source was read or re-fetched.
- Model: the same model as the audit entry above; identifier to be entered by the
  reviewer.
- Prompt: "What are we missing here? The choices you made, nice. You see that it doesn't
  change, it's bound still, does not. Makes sense to me. So let's try to establish what
  we haven't established, with the exception of the page numbers. If it's not already in
  the information, I don't think I have it." (reviewer). Read as: the choices made in
  applying D5 are accepted; settle the items the report lists as not established, page
  numbers excepted; say what is missing.
- What the model did: built the models MH, MS and MT (the last after reporting, to turn an
  inference in finding F8 into a checked model) and proved that the sentence-position
  package without CL.PROP has no finite model (isabelle/Separation_Models.thy); proved
  each puzzle from the admissibility of the one witness it uses, and Fine's universal
  package refuted with typed truth entries (isabelle/Puzzle_Packages.thy); proved two
  earlier inferences (isabelle/Order.thy); wrote scripts/separations.py and stored seven
  separating models; added findings F7 and F8, the `reviewed` field of D5 and the
  restructured `implications` section to the registry; added section 8 to the generated
  results page and section 11 to the audit report.
- Decisions the model took itself: none that changes a statement. The three COMP pairs
  were moved from the rank pairs to a list of their own. A change to comprehension (one
  entry per witness) is proposed to the reviewer and not made.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/verify_models.py (113 of
  113); the seven separating models re-checked by the independent evaluator.
- Human review: pending.

## 2026-11-28 — Witness entries (registry 0.3.2-draft, decision D9)

- Tool: Claude Code (cloud session), the same project thread as the audit; Isabelle2026
  pinned. No source was read or re-fetched.
- Model: the same model as the audit entry above; identifier to be entered by the
  reviewer.
- Prompt: the reviewer chose the option "Add four witness entries" on a decision card
  asking "Add comprehension entries weaker than C1, one per witness?". The card's text
  for that option: "Each asserts that one witness is admissible; C1 stays and implies
  them. I restate the puzzles with them and try to build the typed-truth model."
- What the model did: defined W_ID, W_TR, W_EM and W_TEM (isabelle/Principles.thy) and
  proved that C1, C2, C3d and C3s imply them (isabelle/Order.thy); proved each puzzle
  with its witness entry (isabelle/Puzzle_Packages.thy); built model MU and restated
  model MT with the entries (isabelle/Separation_Models.thy); added the family WIT,
  decision D9 and finding F9 to the registry and restated five puzzle targets; added the
  entries to the search tables (scripts/driver.py); added section 12 to the audit report.
- Decisions the model took itself, listed in the registry under D9
  (`choices_made_in_applying_it`): a family of its own for the entries; no entry denying
  admissibility; targets restated with the witness entries; the automatic search not
  rerun.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/verify_models.py (113 of
  113); scripts/summarize.py reproduces docs/results.md.

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
  review), candidates P.WILHELM.2021 and P.POGGIOLESI.2022, findings F5-F8 (renumbered F10-F13 and decision D6 when merged onto the audit, 2026-11-28). Session builds,
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

## 2026-11-27 — Follow-ups on the model-certificate review questions

- Tool and model as above.
- Prompt: reviewer's questions on the four choices (re-checking, N3, N4, classicality) and
  "If you haven't checked whether [Fritz 2022] already states the finite case, then check."
- What the model did: read fritz2022 pp. 304-310 and 327-329 (page images) and, through a
  fetch subagent, Fritz "Operands and instances" (RSL 2023) pp. 188-201; added N4_pairs to
  Principles.thy and the locale (the registry's four shapes), proved for every model;
  built model MF (IMM.FRITZ7 with CL.PROP, CL.QUANT, TS.FULL); updated F2 with the
  literature check and MF. Session builds, no sorry/oops/axioms.
- Human review: pending.

## 2026-11-27 — Decisions D7 and D8 applied

- Tool and model as above.
- Prompt: reviewer, "Let's go with option A" (re-checking) and "then we should fix that" (N4 in
  all-true models); housekeeping and encoding gap noted (the latter is repaired in PR #4).
- What the model did: merged the audit branch (registry 0.3.0-draft) into this branch;
  registry 0.5.0-draft with decisions D7 (certificate kinds nitpick+python / isabelle-kernel)
  and D8 (N4 only where CL.PROP holds); model records relabelled (MA-ME at N3, MF and MG at
  N5); lemma MG_N4s; results page column "Certificate". Build passes, no sorry/oops/axioms.
- Human review: pending.

## 2026-11-27 — M1 non-triviality N3 and N4

- Tool and model as above (Claude Code, cloud session; Isabelle2026 pinned).
- Prompt: correction relayed by the coordinator from the certificates thread (M1's record
  claimed N5 with only N1, N2 and N5_chain proved; levels are cumulative).
- What the model did: proved N3 instances for all nine introduction entries of the M1
  package (M1_N3) and N4_pairs (M1_N4_pairs, pair at an atom and its double negation;
  CL.PROP holds, so N4 counts under D8), with a fidelity clause for N4_pairs; corrected the
  M1 record, finding F3 and the changelog.
- Human review: pending.

## 2026-11-28 — Merge of main (PR #4) into this branch; lemma MF_not_IMM_CONJ

- Tool and model as above.
- Prompt: none new from the reviewer; the audit thread noted that PR #4 had merged and
  suggested that model MF separates IMM.FRITZ7 from IMM.CONJ with classical truth.
- What the model did: merged main (registry 0.3.2-draft) into this branch, keeping both
  changelogs under 0.5.0-draft; proved MF_not_IMM_CONJ and MF_separates_IMM
  (isabelle/Separation_Models.thy); proved MG_N4s; relabelled the records M1, MS, MT, MU
  to N2 under the cumulative reading of the levels and D8, keeping the issued value in
  `nontriviality_as_issued`.
- Correction after the audit thread pointed out existing N3 lemmas: added MT_N4s, MU_N4s,
  MT_N3_disj and MS_N3_disj (DISJ.ONE instances with distinct disjuncts) and set MT and
  MU to N5, MS to N3 (N4 excluded by D8). M1 is left to PR #6, which proves its N3 and N4.
  Dated notes added to docs/audit-2026-11-27.md where it calls the classical IMM question
  open.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/verify_models.py;
  scripts/summarize.py regenerates docs/results.md.
- Human review: pending.

## 2026-11-28 — Woods's substantive irreflexivity against the Krämer and Fine targets (registry 0.7.0-draft)

- Tool and model as above (Claude Code, cloud session; Isabelle2026 pinned; the search ran on
  GitHub Actions, workflow search.yml, run 46125372163).
- Prompt: reviewer, 2026-11-28: "First, build that model in Isabelle with the existing method
  [...]. Then define the real test: Fine's packages with IRR.W in place of IRR.F (Woods's
  objections 3 and 5, disjunction and ∀p(p ∨ ¬p)). Run those as a search on GitHub, then
  hand-build models for whatever survives."
- Sources: Woods 2018 pp. 640-645 was read through a web extraction of the open-access PDF
  (page numbers given, only short fragments verbatim); the file is not in the project's
  sources. Paraphrases in the registry are marked as such.
- What the model did: wrote isabelle/Woods_Models.thy (theorems on what IRR.W demands under
  classical truth, Woods's Objection 3, controls with ASYM.P; models MW, MV, MV1-MV3, MY,
  MY2, MZ, MZ2, MQ, MQ2, MX, MX2; ALL.TOT in MV); chose the seven test packages and the
  search set of 229 packages (scripts/woods_targets.py); added a `targets` mode to
  scripts/driver.py and to the search workflow; ran the search and replayed its
  refutations; wrote scripts/woods_report.py and section 9 of the results page; registry
  0.7.0-draft with puzzles.irr_w_tests and findings F14-F17. No entry, statement or decision
  of the registry was changed.
- Reading choices made by the model and flagged for review: which packages count as the
  test (IRR.W for IRR.F and nothing else changed); C2 as the comprehension level for
  Objection 3; ALL.TOT read with tot as a constant function, which does not test Woods's
  reply to Objection 5; the one-world vacuity test (decision D2) throughout.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/replay.py (25 of 26
  recorded refutations replay; the one that does not is covered by woods_obj3_refuted);
  scripts/verify_models.py; scripts/summarize.py regenerates docs/results.md;
  scripts/woods_report.py finds no package both modelled and refuted.
- Not done: models for the packages with IMM.CONJ or IMM.FRITZ7 (14 packages, unknown);
  higher-level models for single identity entries; a literature check on novelty beyond the
  project's sources.
- Human review: pending.
- Addition the same day, after the reviewer supplied page images of Woods 2018 p. 645 with
  fnn. 36-38 and asked whether his comments change the options: the registry's reading
  of p. 645 was checked against the images and extended; Part 11 of
  isabelle/Woods_Models.thy (totality_substitution_false, totality_reply_vacuous,
  totality_one_world, totality_example) and finding F18 were added. The reading of the
  totality fact used there is the model's and is flagged for review; the reviewer's point
  that a list can be treated as a function corrected an earlier claim of the model's.
  Checks: full session build; scripts/check_no_sorry.sh. Human review: pending.

## 2026-11-28 — Woods's proposal without totality facts; level corrections (registry 0.7.0-draft, finding F19)

- Tool and model as in the entry above on Woods's substantive irreflexivity (Claude Code, cloud
  session; Isabelle2026 pinned).
- Prompt: reviewer, 2026-11-28: "do option 4 as well", option 4 being the model's own proposal
  to test Woods without totality facts under a constraint that only rule-generated grounds
  exist.
- AI contribution: the design of the model MR (structured propositions as a datatype with
  closures, classical truth by evaluation over truth values, ground as an inductive
  definition), every proof in isabelle/Rule_Generated.thy, finding F19, the proposed entry
  proposed.GEN.RULES and its flagged readings. The choice of rules, the reading of
  "rule-generated" and the comparison with Woods's reply are the model's and are pending
  review. The claim that a failure of the one-world test is a failure of Woods's modal test,
  and the claim that the test is trivial without its third clause, are inferences that
  Isabelle did not check.
- Correction made by the model to its own earlier work in this version: the records of MV, MY
  and MZ claimed N5 with N3 instances for only some of their introduction entries. Missing
  instances proved (MV_N3_more, MY_N3_more, MZ_N3_more); records of MV1-MV3 split, with
  CONJ.INF at N2. One package of the search set moved from N5 to N2.
- Checks: full session build; scripts/check_no_sorry.sh; scripts/woods_report.py;
  scripts/verify_models.py; scripts/summarize.py regenerates docs/results.md.
- Human review: pending.

## 2026-11-28 — Search results open their own pull request

- Tool: Claude Code (cloud session), project thread "Automate search results PRs". Model:
  claude-opus-5-5 (configured id; serving model not independently confirmed).
- Prompt: the coordinator's brief, relaying that the reviewer created a fine-grained token
  saved as the Actions secret RESULTS_PR_TOKEN: when the search workflow finishes it should
  commit its results to a branch and open a pull request against main with that token, so
  that the required isabelle check runs; fail loudly if the secret is missing or expired;
  leave the run in progress (46120076428) alone.
- What the model did: added scripts/publish_results.sh (token check, choice of base, merge,
  re-verification, regeneration of docs/results.md, push, pull request), a token job that
  gates the search, a token_check_only input, and a local test against a stand-in remote and
  API (scripts/tests/). Ranked refuted-at-N1 above unknown in scripts/merge_results.py (the
  same one-line change as on the Woods branch).
- Checks: scripts/tests/publish_results_test.sh (six cases pass); token check run on GitHub
  (see the pull request).
- Human review: pending.
