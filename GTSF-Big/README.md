# Big-step semantics and DGG for GTSF

## Status and scope

This directory is a design draft. It does not replace `GTSF/NuReduction.agda`
or claim a proof of the dynamic gradual guarantee. It gives:

- a structural, call-by-value big-step judgment in `BigStep.agda`;
- checked semantic exercises in `BigStepExamples.agda`;
- the induced termination observations in `BigStepObservations.agda`;
- the exact adequacy boundary in `BigStepProperties.agda`; and
- a checked big-step DGG statement in
  `BigStepDynamicGradualGuarantee.agda`.

The draft reuses the existing Nu syntax, compilation, typing, imprecision,
and store-world relations. This isolates the semantic experiment from the
language definition.

## Why the judgment returns a store-change trace

A judgment of the form `M ⇓ V` is too weak for GTSF. Evaluating `ν A L c`
allocates a fresh runtime type name. In the existing semantics this emits
`bind A`, increases the type context, extends the store, and renames every
piece of syntax that survives the allocation.

The draft therefore uses

`M ⇓[ χs ] R`,

where `χs : StoreChanges` and `R` is a value or `blame`. The old and new
semantics interpret the same trace with `applyTyCtxs`, `applyStores`,
`applyTys`, and `applyTerms`. Consequently, the final DGG value relation can
retain its existing world:

`StoreImp Φ (applyTyCtxs χs Δᴸ) (applyTyCtxs χs′ Δᴿ)`.

The trace currently records `keep` as well as `bind`. This makes exact
adequacy possible:

`M ⇓[ χs ] R` if and only if `M —↠[ χs ] R` and `R` is final.

An allocation-only trace would be smaller, but its adequacy theorem would
need a trace-erasure relation and would add no value to the first draft.

## Structural evaluation

The semantics is not a synonym for multi-step reduction. Its recursive rules
follow the call-by-value structure of the term. It reuses `_—→_` only for a
single pure contraction after the operands of a redex have been evaluated.
Moving the pure redex relation into a module shared by `NuReduction` and
`BigStep` would remove even this small dependency later.

For application, the successful rule has the following shape:

1. `L ⇓[ χsL ] V`;
2. `applyTerms χsL M ⇓[ χsM ] W`;
3. `applyTerms χsM V · W —→ N`;
4. `N ⇓[ χsN ] R`; and
5. `L · M ⇓[ χsL ++ χsM ++ keep ∷ χsN ] R`.

The two applications of `applyTerms` are essential. Allocations while
evaluating `L` shift the suspended argument `M`; allocations while evaluating
that argument shift the already-computed function value `V`. Primitive
application uses the same pattern. The rules also carry `TraceShiftable`
evidence for both phases. It is the trace-level closure of the small-step
`Shiftable` side condition, so the semantics agrees with small-step reduction
even on raw terms; it does not silently appeal to the stronger `RuntimeOK`
invariant of compiled programs.

For a cast `M ⟨ c ⟩`, evaluation first obtains
`M ⇓[ χs ] V`. The residual coercion is `applyCoercions χs c`.
If it is inert, `V ⟨ applyCoercions χs c ⟩` is the result. Otherwise one
pure root reduction is performed and evaluation continues. If the inner
evaluation returns `blame`, the outer blame-propagation step is recorded.

For `ν A L c`, evaluation first obtains `L ⇓[ χs ] V`. Allocations made
inside `L` transform the binder annotation to `applyTys χs A`. They transform
`c` below its type binder with `applyCoercionsUnderTyBinders`, which is
different from ordinary `applyCoercions`. The allocation then emits
`bind (applyTys χs A)` and evaluation continues with

`((⇑ᵗᵐ V) •) ⟨ applyCoercionsUnderTyBinders χs c ⟩`.

There is no congruence rule below runtime type application `_•`. This matches
`RuntimeOK`: a compiled runtime bullet contains an already-computed value and
contracts at the root.

## Results, convergence, and divergence

The inductive judgment describes only finite evaluations and proves that
every result is a `Value` or `blame`.

The observations are:

- `ValueConvergesᵇ M`: `M` evaluates to a value;
- `Blamesᵇ M`: `M` evaluates to `blame`;
- `Convergesᵇ M`: `M` has some finite big-step derivation;
- `Divergesᵇ M = ¬ Convergesᵇ M`; and
- `DivergesOrBlamesᵇ M = ¬ ValueConvergesᵇ M`.

The final negative definition is deliberate. Constructively, a proof that a
program does not return a value need not choose between an infinite run and a
finite blame result. For closed, well-typed compiled terms, progress,
preservation, determinism, and big-step adequacy justify reading it as
"diverges or blames." If productive evidence of divergence is needed later,
add a separate coinductive judgment rather than complicating finite
evaluation.

As in the existing `Divergesᶜ`, a stuck raw term satisfies the negative
divergence definition. The DGG ranges over compiled, closed, typed terms, for
which the runtime progress invariant rules out that case.

## Big-step formulation of the DGG

Let `N` and `N′` be the compiled left and right programs. The direct big-step
translation of the current four-part DGG is:

1. If `N ⇓[ χs ] V` and `V` is a value, then
   `N′ ⇓[ χs′ ] V′` for a related value `V′`.
2. If `N` diverges, then `N′` diverges.
3. If `N′ ⇓[ χs′ ] V′` and `V′` is a value, then either
   `N ⇓[ χs ] V` for a related value `V`, or `N ⇓[ χs ] blame`.
4. If `N′` diverges, then `N` cannot return a value; on a closed typed
   program, `N` therefore diverges or blames.

The related-value alternatives retain the full final package from the
small-step statement: final type contexts, transformed result types, final
stores, `StoreImp`, the proof-relevant type-imprecision witness, and
`QuotientedTermImprecision` between the two values.

The asymmetry is intentional. The third and fourth clauses permit blame on
the left in the direction already present in the public theorem. The first
clause remains strict. Its plausibility depends on the current eager
`GenSafe` repair; an older unrestricted `gen` grammar admitted the
mismatched-tag counterexample recorded in the DGG proof log.

## Proof plan

The next proof work should proceed in this order.

1. Prove that type renaming by `applyTerms` preserves `Value` and `No•`.
2. Prove multi-step frame lemmas that concatenate traces and apply allocation
   shifts to the suspended parts of application, primitives, casts, and `ν`.
3. Prove `BigStepAdequacy.sound` by induction on the big-step derivation.
4. Prove `BigStepAdequacy.complete` by induction on a terminating small-step
   trace, using determinism and evaluation-context inversion to recover the
   structural subderivations.
5. Transport the existing small-step DGG across adequacy. This validates the
   statement without duplicating the current simulation proof.
6. Only then assess whether a direct proof by induction on a big-step
   derivation is shorter. Such a proof should still reuse the existing
   world-extension and catch-up lemmas at allocation and active-cast cases.

The checked examples already cover term beta, primitive addition, successful
and failing tag checks, and a `ν` allocation trace. The next useful milestone
is soundness. Completeness is the harder direction because a flat small-step
trace must be decomposed back into its evaluation-context phases.
