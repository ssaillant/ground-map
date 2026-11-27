# Ground Map

**Which principles of metaphysical ground can be held together, and which cannot?**

The logic of ground has a family of paradoxes. Fine's puzzles (2010), Krämer's simpler puzzle (2013), Fritz's Cantor-style results (2020, 2022) and Korbmacher's diagonal puzzle (2015) all show that principles each of which looks compelling, such as "a true existential is grounded in its true instances" and "nothing grounds itself", cannot all be true. The usual responses each give up something different: irreflexivity (Correia, Woods), unrestricted existential grounding (Krämer), β-conversion (Fritz, Wilhelm), classical logic, or fine-grained propositional identity.

This project treats the debate as a map. Every principle in the literature is stated once, precisely, with its source and page. Every *package* (a combination of principles) is then classified by machine: either Isabelle/HOL checks a proof that the package is inconsistent, or a model shows that it is consistent, or the package is marked unknown. The goal is to see exactly what each puzzle needs, which responses really escape it, and whether consistent, non-trivial packages exist that nobody has yet defended.

**Current results: [docs/results.md](docs/results.md)**. That page is generated from the data and is provisional.

## How to read a result

- **refuted**: Isabelle has checked a proof that the package is inconsistent. Each search refutation is replayed in `isabelle/Results_Refutations.thy`, and the published puzzles are proved in their own theories (see below).
- **trivial-only**: the package is consistent only if nothing grounds anything.
- **finite-model**: a finite model was found by Nitpick and re-checked by a second, independent implementation of the semantics (`scripts/verify_models.py`).
- **infinite-model**: an infinite model built in Isabelle. Many packages of interest have no finite model (finding F1), so this class matters. None exist yet.
- **unknown**: no proof and no model within the time limits. Unknown never means consistent.

Consistency is always tested together with a non-triviality floor (at least one grounding fact). Stronger floors N2–N5 are defined in the registry.

## Where things live

| Path | What it is |
|---|---|
| `principles/registry.yaml` | **The philosophical core.** About 45 principles in 18 families, each with a source quotation and page, a formal statement, and every reading choice made. Also the decisions D1–D4, the puzzle targets, the findings and the bibliography. |
| `isabelle/Signature.thy` | The formal language: propositions as a base type, a truth predicate, strict full ground between a set of propositions and a proposition, and a formula layer for λ-terms. |
| `isabelle/Principles.thy` | Every registry principle as an Isabelle definition. |
| `isabelle/Order.thy` | Proved implications between principles, the only ones the search uses. |
| `isabelle/Russell_Checks.thy`, `Fine_Checks.thy`, `Fritz_Main.thy`, `Fritz2020_Checks.thy`, `Korbmacher_Checks.thy` | The published puzzles, machine-checked. |
| `isabelle/No_Finite_Models.thy` | Finding F1. |
| `isabelle/Results_Refutations.thy` | Refutations found by the search, replayed and checked (generated). |
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

Registry v0.2.1-draft. Every published puzzle is reproduced except Woods's check, which stays open as a target. Search runs are just starting. No candidate novel result yet; see section 6 of the results page for what would count as one.

## Build locally

    isabelle build -v -D isabelle
    python3 scripts/summarize.py
