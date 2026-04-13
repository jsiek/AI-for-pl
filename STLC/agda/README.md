# STLC/agda note

This directory contains the Agda development for the simply typed lambda
calculus with natural numbers and case analysis.

## Public/audited surface (`STLC/agda/`)

The top-level files are organized as the trust-facing interface:

- `STLC.agda`: core language definition (types, terms, typing, reduction,
  and multi-step closure).
- `TypeSafety.agda`: public theorem statements/wrappers for `typeSafety`
  (and supporting wrappers used by `Eval`).
- `Termination.agda`: public theorem statement/wrapper for `termination`.
- `TypeCheckDec.agda`: public theorem statement/wrapper for `type-check`.
- `Examples.agda`: executable/typed example suite (kept at top level as a
  trust-facing artifact).
- `Eval.agda`: fuel-bounded evaluator.
- `All.agda`: aggregate driver.

## Private proof implementation (`STLC/agda/proof/`)

Proof-heavy material now lives under `proof/`:

- `proof/TypeSafety.agda`: progress/preservation development and the core
  type-safety proof.
- `proof/Termination.agda`: logical-relations termination proof.
- `proof/TypeCheckDec.agda`: implementation proof of decidable type checking.
- `proof/Subst.agda`: substitution algebra and commuting lemmas.
- `proof/TypingLemmas.agda`: typing uniqueness, lookup, and inversion helpers.
- `proof/CoreLemmas.agda`: helper lemmas (`multi-trans`, `_≟Ty_`) used only by proofs.

Top-level theorem modules are thin wrappers around these `proof/*` theorems,
so audit reading can focus on language definitions and theorem statements first.
