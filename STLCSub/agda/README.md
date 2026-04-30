# STLCSub/agda note

This directory contains an Agda development for the simply typed lambda
calculus with naturals, `Top`, subtyping, records, and record projection.
The source design follows the TAPL Chapter 15/16 presentation: function
subtyping is contravariant in the domain and covariant in the codomain, and
record subtyping supports width, depth, and permutation through field lookup.

## Public/audited surface (`STLCSub/agda/`)

- `STLCSub.agda`: core language definition, subtyping, typing, substitution,
  values, reduction, and multi-step closure.
- `Eval.agda`: executable fuel-bounded evaluator.
- `TypeCheckDec.agda`: algorithmic subtyping and executable type checking.
- `Examples.agda`: typed examples and evaluator checks.
- `MetaTheory.agda`: public progress, preservation, and type-safety statements.
- `All.agda`: aggregate driver. Run Agda on this file to check the folder.
- `Design.md`: informal language notes.

## Private proof implementation (`STLCSub/agda/proof/`)

- `proof/TypeSafety.agda`: proof boundary for progress/preservation and
  multi-step type safety.
