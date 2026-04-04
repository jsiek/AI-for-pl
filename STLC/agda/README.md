# STLC/agda note

This directory contains the Agda development for the simply typed lambda
calculus with natural numbers and case analysis.

The main ingredients are:

- `STLC.agda`: syntax, typing, renaming/substitution, values, and small-step reduction.
- `Subst.agda`: substitution algebra and commuting lemmas.
- `TypeSafety.agda`: progress, preservation, and related typing lemmas.
- `Eval.agda`: a fuel-bounded evaluator that returns a trace and value witness.
- `Examples.agda`: source-inspired examples plus coverage cases for every reduction rule.

Design emphasis:

- Use parallel renaming and parallel substitution as the core infrastructure.
- Derive single-substitution as a special case.
- Keep examples close to classical TAPL/PLFA STLC shapes so they double as regression tests.
