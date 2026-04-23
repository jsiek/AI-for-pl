# STLC/agda TODO ("done" and missing)

This checklist records what appears complete in `STLC/agda` and what is still missing.

## Already done

- [x] Core syntax and typing are defined in `STLC.agda`.
- [x] Small-step reduction and multi-step closure are defined in `STLC.agda`.
- [x] Parallel renaming/substitution infrastructure is present in `STLC.agda`.
- [x] Single substitution is derived from parallel substitution (`singleEnv`, `singleSubst`).
- [x] Substitution metatheory is developed in `proof/Subst.agda`.
- [x] Progress and preservation are proved in `TypeSafety.agda`.
- [x] Cross-check exists in Lean (`STLC/lean`).

## Missing items to reach "done"

## Core deliverables

- [x] Add `Eval.agda` with an executable evaluator for STLC terms.
- [x] Add `Examples.agda` with representative well-typed closed examples.
- [x] Add explicit reduction/evaluation traces in examples.
- [x] Add regression examples for substitution-under-binders.
- [x] Add a compact `TypeSafety` wrapper theorem API (closed-term safety packaging).
- [x] Add a brief local design/proof note (`README.md` or notes file) in `STLC/agda`.

## Example sourcing (requested)

- [x] Add TAPL-inspired examples from the STLC chapter.
- [x] Add PLFA-inspired examples from https://plfa.github.io/ (STLC-relevant patterns).
- [x] Keep source attribution comments near examples indicating TAPL/PLFA lineage.

## Reduction coverage requirement for examples

Examples should collectively exercise all STLC reduction rules in `STLC.agda`.

- [x] `xiAppLeft`
- [x] `xiAppRight`
- [x] `betaLam`
- [x] `xiSuc`
- [x] `xiCase`
- [x] `betaZero`
- [x] `betaSuc`

## Termination/normalization track

`Termination.agda` currently relies on postulates. Drive this toward mechanized completion.

- [x] Replace `VNat_to_Value` postulate with proof.
- [x] Replace `𝒱_to_Value` postulate with proof.
- [x] Replace `app_compat` postulate with proof.
- [x] Replace `suc_compat` postulate with proof.
- [x] Replace `case_compat` postulate with proof.
- [x] Replace `fundamental_property` postulate with proof.

## Block handling convention

If an item is blocked during implementation:

- Mark it as `- [B] ...` with a concise blocker note inline.
- Add a longer handoff log under `SystemF/log/` with:
  - exact goal,
  - attempted approach,
  - current proof state/errors,
  - and any copied snapshots needed to resume work.
