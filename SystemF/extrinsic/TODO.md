# SystemF/extrinsic TODO ("done" checklist)

This checklist defines what "done" means for `SystemF/extrinsic`.

## Core deliverables

- [x] Add `Eval.agda` with an executable evaluator for extrinsic terms.
- [x] Add `Examples.agda` with at least 12 representative, well-typed, closed examples.
- [x] Add explicit evaluation/reduction traces for examples (expected outcomes).
- [x] Add regression examples for substitution-under-binders and polymorphic instantiation/application.
- [x] Add `TypeSafety.agda` with a wrapper theorem that packages `progress + preservation`.
- [x] Keep a design note documenting major deviations and proof strategy.
  Current note: `SystemF/extrinsic/README.md`.

## Example sourcing plan

- [x] Source examples first from this repo:
  `SystemF/intrinsic/FreeTheorems.agda`,
  `SystemF/intrinsic/Reduction.agda`,
  `SystemF/intrinsic/Terms.agda`,
  and erase/adapt to extrinsic form when useful.
- [x] Add examples inspired by TAPL's System F chapter.
- [x] Add Wadler-style free-theorem examples (identity/representation-independence patterns).
- [x] Ensure the final 12+ examples are mixed:
  polymorphism (`Λ`/`·[]`), functions, booleans, naturals, conditionals, and case.

## Complete reduction-rule coverage requirement

Goal: collective examples must exercise every reduction rule in `extrinsic/SystemF.agda`.

- [x] `ξ-·₁`
- [x] `ξ-·₂`
- [x] `β-ƛ`
- [x] `ξ-suc`
- [x] `ξ-if`
- [x] `ξ-case`
- [x] `β-true`
- [x] `β-false`
- [x] `β-zero`
- [x] `β-suc`
- [x] `ξ-·[]`
- [x] `β-Λ`

## Coverage evidence to include

- [x] For each rule above, include at least one named example whose first step uses that rule.
- [x] Record expected one-step result for each rule-targeting example.
- [x] For each example, include a multi-step reduction/eval endpoint (value form or normal form).
- [x] Keep a simple coverage index in `Examples.agda` mapping `rule -> example-name`.
