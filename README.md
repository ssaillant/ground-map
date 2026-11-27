# Ground Map

**Which principles of metaphysical ground can be held together, and which cannot?**

The logic of ground has a family of paradoxes. Fine's puzzles (2010), Krämer's simpler puzzle (2013), Fritz's Cantor-style results (2020, 2022) and Korbmacher's diagonal puzzle (2015) all show that principles each of which looks compelling, such as "a true existential is grounded in its true instances" and "nothing grounds itself", cannot all be true. The usual responses each give up something different: irreflexivity (Correia, Woods), unrestricted existential grounding (Krämer), β-conversion (Fritz, Wilhelm), classical logic, or fine-grained propositional identity.

This project treats the debate as a map. Every principle in the literature is stated once, precisely, with its source and page. Every *package* (a combination of principles) is then classified by machine: either Isabelle/HOL checks a proof that the package is inconsistent, or a model shows that it is consistent, or the package is marked unknown. The goal is to see exactly what each puzzle needs, which responses really escape it, and whether consistent, non-trivial packages exist that nobody has yet defended.

**Current results: [docs/results.md](docs/results.md)**. That page is generated from the data and is provisional.

## How to read a result

- **refuted**: Isabelle has checked a proof that the package is inconsistent. Each search refutation is replayed in `isabelle/Results_Refutations.thy`, and the published puzzles are proved in their own theories (see below).
- **refuted at N1**: Isabelle has checked a proof that the package is inconsistent with at least one grounding fact, and no refutation of the package itself was found. This is not a consistency claim. The package is consistent (only in models where nothing grounds anything) where the results page also reports a verified model at N0. Until registry 0.3.0-draft this class was called trivial-only.
- **finite-model**: a finite model was found by Nitpick and re-checked by a second, independent implementation of the semantics (`scripts/verify_models.py`), or, for principles about the formula layer, built and checked in Isabelle (`isabelle/Model_Certificates.thy`, `isabelle/Restricted_Models.thy`).
- **infinite-model**: an infinite model built in Isabelle. Many packages of interest have no finite model (findings F1, F2), so this class matters. The first ones are in `isabelle/Model_Certificates.thy` (IMM.FRITZ7) and `isabelle/Models.thy` (term model M1, finding F3).
- **unknown**: no proof and no model within the time limits. Unknown never means consistent.

Consistency is always tested together with a non-triviality floor (at least one grounding fact). Stronger floors N2–N5 are defined in the registry.

Every registry entry is standalone: a package contains exactly the entries listed. The only implications between entries are those proved in `isabelle/Order.thy` and listed in the registry section `implications`.

## Where things live

| Path | What it is |
|---|---|
| `principles/registry.yaml` | **The philosophical core.** About 45 principles in 18 families, each with a source quotation and page, a formal statement, and every reading choice made. Also the decisions D1–D4, the puzzle targets, the findings and the bibliography. |
| `isabelle/Signature.thy` | The formal language: propositions as a base type, a truth predicate, strict full ground between a set of propositions and a proposition, and a formula layer for λ-terms. |
| `isabelle/Principles.thy` | Every registry principle as an Isabelle definition. |
| `isabelle/Order.thy` | Proved implications between principles, the only ones the search uses. |
| `isabelle/Russell_Checks.thy`, `Fine_Checks.thy`, `Fritz_Main.thy`, `Fritz2020_Checks.thy`, `Korbmacher_Checks.thy` | The published puzzles, machine-checked. |
| `isabelle/Puzzle_Packages.thy` | Krämer's and Fine's puzzles proved from the registry's own entries, with the partial-ground premises the sources use (registry 0.3.0). |
| `isabelle/No_Finite_Models.thy` | Finding F1. |
| `isabelle/Models.thy` | Term model M1 with hyperintensional application: a classical package of 20 registry entries (plus FACT and LAM_CORE) with transitive, irreflexive ground and impredicative comprehension (finding F3), and Goodman's negation variant of Krämer's puzzle (finding F4). |
| `isabelle/Results_Refutations.thy` | Refutations found by the search, replayed and checked (generated). |
| `isabelle/Model_Certificates.thy` | Models built in Isabelle: the signature as a locale with every constant a parameter, a proof that its definitions are the registry's, models for the principles the search could not settle, and finding F2. Records in `results/isabelle_models.jsonl`. |
| `isabelle/Restricted_Models.thy` | Model MG: the restricted entries (EX.PRED, EX.LEV, TS.TYPED, TR.TYPED) hold together with classical truth while the unrestricted ones fail (finding F5). |
| `isabelle/Audit_Checks.thy` | Evidence for the audit of 2026-11-27: the 0.2.x definitions of the restricted entries collapsed into the unrestricted ones. |
| `docs/audit-2026-11-27.md` | Independent audit of the registry against the sources, and the repairs made in 0.3.0. |
| `scripts/driver.py` | The search: asks Sledgehammer for refutations and Nitpick for models, then propagates results along proved implications. |
| `results/` | Raw search output (`queries.jsonl`), replay and model-verification records. |
| `docs/results.md` | The generated summary. Do not edit by hand. |
| `AI_USE_LOG.md` | Prompts, models and human review, for AI-use disclosure. |
| `TOOLS.md` | Pinned tool versions. |

## Design decisions

These are stated in full in the registry (`decisions`).

- **D1**: immediate ground is defined from mediate ground.
- **D2**: Woods's vacuity test is read by uniform substitution.
- **D3**: λ-terms and β-principles form a family of their own, so schematic and quantified principles can be compared. Fritz 2020's analysis of Krämer's puzzle turns on exactly this.
- **D4**: an infinite-model class, certified by models built in Isabelle.

## Rules

Nothing reported as done contains `sorry`, `oops` or extra axioms. CI enforces this, builds every theory with the pinned Isabelle2026, and regenerates `docs/results.md`. Long searches run as GitHub Actions on `search/...` branches.

## Status (2026-11-27)

Registry v0.2.1-draft. Every published puzzle is reproduced except Woods's check, which stays open as a target. Search runs are just starting. The first infinite-model certificate (term model M1, finding F3) checks, but it is not a candidate novel result: Goodman 2023 already gives a consistent theory of this kind. No candidate novel result yet; see section 7 of the results page for what would count as one.

## Build locally

    isabelle build -v -D isabelle
    python3 scripts/summarize.py
