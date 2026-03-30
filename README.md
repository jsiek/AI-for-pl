# AI-for-pl

experiments in using AI (GPT-5.3-Codex) to do PL metatheory

STLC - Simply Typed Lambda Calculus

lambda - Untyped lambda calculus

GTLC - Gradually Typed Lambda Calculus

System F - Polymorphic Lambda Calculus

GTSF - Gradually Typed System F

PolyCast - A polymorphic cast calculus with intrinsically typed
coercions that include coercions to and from universal types, that is,
generalization and instantiation.


# Agda Development Notes

## Agda `with` style (from 2026-03-24)

For `with` clauses, if there are two or more cases, use explicit
function-name case clauses rather than `...` shorthand. 
This will avoid problems that arise with nested `with` clauses.

## Agda recursive function termination / `with` style (from 2026-03-24)

Agda termination checking can be tripped by helper functions that took
the recursive function as a higher-order argument.

Working fix:

- Inline those helpers instead of passing recursive function as an argument.
- For nested `with` clauses, use explicit function-name case clauses rather than `...` shorthand.
  (Problems with nested `with` clauses may have been the reason for introducing the helper
   in the first place.)

This avoids confusing Agda's termination checker and keeps recursive
functions accepted without `{-# TERMINATING #-}`.
