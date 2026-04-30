# STLCMore/agda note

This directory contains the Agda development for the simply typed lambda
calculus with natural numbers, Unit, and case analysis, plus a derived
sequencing form.

The sequencing form is defined as a derived term constructor:
`M ； N = (ƛ unit ⇒ rename suc N) · M`.

## Public/audited surface (`STLCMore/agda/`)

The top-level files contain the definitions and theorem statements
that you must read to undestand and trust these results about the
STLCMore.

- `STLCMore.agda`: core language definition (types, terms, typing, reduction,
  and multi-step closure).
- `MetaTheory.agda`: public metatheory theorem statements for
  `preservation`, `progress`, `type-safety`, and `termination`.
- `TypeCheckDec.agda`: public theorem statement/wrapper for `type-check`.
- `Examples.agda`: executable/typed example suite.
- `Eval.agda`: fuel-bounded evaluator.
- `All.agda`: aggregate driver. Run agda on this file to check everything.

## Makefile checks

Use the `Makefile` in this directory to run the trust checks:

- `make check`: runs all checks below.
- `make agda`: runs `agda -v0 All.agda`.
- `make postulate-check`: greps for `"postulate"` in `*.agda` and `proof/*.agda`.

## Private proof implementation (`STLCMore/agda/proof/`)

The files in the proof/ directory have been checked by Agda so you
don't have to read them to believe the results. You just need to grep
for "postulate" and check that the Agda flags that introduce
inconsistency are not enabled. The `Makefile` includes the grep for postulates.

Of course, you may want to read these proofs to understand and learn
about the proof techniques!

- `proof/TypeSafety.agda`: progress/preservation development and the core
  type-safety proof.
- `proof/Termination.agda`: logical-relations termination proof.
- `proof/TypeCheckDec.agda`: implementation proof of decidable type checking.
- `proof/Subst.agda`: substitution algebra and commuting lemmas.
- `proof/TypingLemmas.agda`: typing uniqueness, lookup, and inversion helpers.
- `proof/CoreLemmas.agda`: helper lemmas (`multi-trans`, `_≟Ty_`) used only by proofs.

Top-level public theorem modules (`MetaTheory.agda` and `TypeCheckDec.agda`)
are thin wrappers around these `proof/*` theorems, so audit reading can focus
on language definitions and theorem statements.
