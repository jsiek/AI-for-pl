# STLCRef/agda note

This directory contains the Agda development for STLC with mutable
references (`STLCRef`) in the style of TAPL Chapter 13.

## Public/audited surface (`STLCRef/agda/`)

- `STLCRef.agda`: core language definition (types, terms, renaming/substitution,
  typing with store typing, values, and small-step reduction over configurations).
- `Eval.agda`: fuel-bounded evaluator wrapper.
- `Examples.agda`: executable, typed examples adapted from TAPL Chapter 13.
- `MetaTheory.agda`: public wrappers for progress, preservation, and type safety.
- `All.agda`: aggregate driver. Run agda on this file to check everything.

## Makefile checks

- `make check`: runs all checks below.
- `make agda`: runs `agda -v0 All.agda`.
- `make postulate-check`: greps for `postulate` in `*.agda` and `proof/*.agda`.

## Private proof implementation (`STLCRef/agda/proof/`)

- `proof/Eval.agda`: private evaluator implementation (`value?`, `step?`, `eval`).
- `proof/TypeSafety.agda`: progress/preservation/type-safety with store typing.
