# STLCRec/agda note

This directory contains the Agda development for the simply typed lambda
calculus with naturals, case analysis, and recursive functions (`STLCRec`).

## Public/audited surface (`STLCRec/agda/`)

- `STLCRec.agda`: core language definition (types, terms, de Bruijn renaming/
  substitution, typing, values, and reduction).
- `Examples.agda`: typed/reduction examples including a `μ`-recursive term.
- `MetaTheory.agda`: proof of type safety via the fundamental theorem
   of a logical relation.
- `All.agda`: aggregate driver. Run agda on this file to check everything.

## Private proof implementation (`STLCRec/agda/proof/`)

- `proof/Subst.agda`: substitution algebra and commuting lemmas.
- `proof/Fundamental.agda`: step-indexed logical relation and proof of the
  fundamental theorem.

## Makefile checks

- `make check`: runs all checks below.
- `make agda`: runs `agda --safe -v0 All.agda`.
- `make postulate-check`: greps for `postulate` in `*.agda` and `proof/*.agda`.
