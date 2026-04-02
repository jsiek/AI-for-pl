# AI-for-pl

Experiments in using AI (GPT-5.3-Codex) to do PL metatheory

STLC - Simply Typed Lambda Calculus

lambda - Untyped lambda calculus

GTLC - Gradually Typed Lambda Calculus

System F - Polymorphic Lambda Calculus

GTSF - Gradually Typed System F

PolyCast - A polymorphic cast calculus that is intrinsically typed and
uses coercions to express casts between types. Coercions can cast to
and from universal types, that is, generalization and instantiation.

PolyUpDown - A polymorphic cast calculus that splits imprecision into
two relations, widening and narrowing, and uses them to express casts
between types. The Agda development proves PolyUpDown type safe.

PolyImp - A polymorphic cast calculus that is intrinsically typed and
uses imprecision to express casts between types.  Imprecision allows
casts to and from universal types, that is, generalization and
instantiation. The Agda development proves PolyImp type safe.

PolyBlameI - A failed attempt at a polymorphic cast calculus that uses
imprecision. This design is not type safe because type substitution
does not preserve imprecision typing.

# Work in Progress



# Agda Development Notes

## Use "constructor form indices" for data type constructors (from 2-26-03-30)

In Agda, constructor form indices are indices of an indexed data type
that are expressed using only data constructors (like zero, suc, [],
or _∷_) and variables, rather than defined functions (like addition
_+_ or maximum max). Adhering to this form is crucial because Agda's
built-in unification algorithm has difficulty solving equality
problems involving user-defined functions that do not immediately
reduce to a constructor-based form.

To resolve "cannot unify" or "I'm not sure if there should be a case"
errors caused by complex indices, you should refactor your data types
and proofs.  Avoid Functions in Indices: If a type has a function call
in its index, for example, max n m ≤ u, the unifier will struggle to
match max n m with other terms (e.g., n + k).  Use Equality Proofs
Internally: Instead of an index f(x), use an explicit equality proof
within the data type's definition to relate the function's result to
the expected value. The type could become something like D : A → Set
where a constructor takes an argument of type f x ≡ y.

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
