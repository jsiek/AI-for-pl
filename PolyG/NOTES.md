# PolyG Development Notes

## Agda recursive function termination / `with` style (from 2026-03-24)

Agda termination checking was previously tripped by helper functions
that took the recursive function as a higher-order argument (for
example, `PolyGEval.agda` use to pass `stepC` into local helpers).

Working fix:

- Inline those helpers instead of passing recursive function (e.g. `stepC`) as an argument.
- For nested `with` clauses, use explicit function-name case clauses rather than `...` shorthand.
  (Problems with nested `with` clauses may have been the reason for introducing the helper
   in the first place.)

This avoids confusing Agda's termination checker and keeps recursive functions (e.g. `stepC`)
accepted without `{-# TERMINATING #-}`.
