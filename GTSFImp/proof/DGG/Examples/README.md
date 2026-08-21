# DGG source examples

This directory contains one independently checked Agda module for each
source-program pair used to justify the cast-term imprecision relation and its
preservation by reduction.  The examples are ordered by increasing operational
and world complexity.

The displays below use names for variables and spell out the programs rather
than referring to Agda helper definitions.  Source blame labels are omitted
because they do not affect the term shapes under discussion.

Each source-example module should contain:

- the two closed source terms;
- a typing derivation for each term;
- their gradual term-imprecision derivation;
- the ordinary compiler output and its typing derivation;
- whole-term reduction chains to first-order results;
- an initial simulation checkpoint and one checkpoint after every source-side
  reduction, with zero or more target catch-up steps between checkpoints;
- a cast-term-imprecision derivation at every checkpoint; and
- the generated, pinned `ImpLadder` output for every checkpoint.

Each file must check independently.  A red example does not count as evidence
for retaining or changing a cast-term-imprecision rule.

If a checkpoint exposes a genuine CTI obstruction, record its outside-in
ladder with `?` exactly at the first unavailable rule or alignment fact.  The
partial ladder must still use the row and table rendering from
`proof.DGG.ImpLadder`; do not draw a second table by hand.  When the obstruction
is resolved, replace the `?` with the closed derivation row and pin the complete
generated ladder.

When a checkpoint derivation has a choice, it uses the two-sided CTI rule for
casts, conversions, type abstractions, and type applications.  A one-sided
rule is used only when the two endpoint terms genuinely have different outer
forms.  In particular, matched conversion boundaries are represented by one
paired node, not by two unrelated one-sided nodes.

## Initial list

### 1. `ConstantRefl.agda`

Source pair:

`42 ⊑ 42`

Both terms have type `ℕ` and evaluate to `42`.

### 2. `LambdaArgumentPrecision.agda`

Source pair:

`((λ x : ℕ. x) 42) ⊑ ((λ x : ★. x) 42)`

Expected compiled pair:

`((λ x. x) (42 ⟨ idℕ ⟩)) ⊑ ((λ x. x) (42 ⟨ ℕ ! ⟩))`

The left result has type `ℕ`; the right result has type `★`.  Both
executions return the natural number `42`, with the right result tagged as
dynamic.

### 3. `MonomorphicFunctionCast.agda`

Source pair:

`((λ f : ℕ ⇒ ℕ. f 42) (λ x : ℕ. x))`
`⊑ ((λ f : ★ ⇒ ★. f 42) (λ x : ℕ. x))`

The right compilation casts the argument function from `ℕ ⇒ ℕ` to
`★ ⇒ ★`, then casts `42` to `★`.  This is the basic monomorphic
function-cast example.  The final results are `42 : ℕ` and tagged `42 : ★`.

### 4. `MatchedInstantiation.agda`

Source pair:

`(((Λ X. λ x : X. x) [ℕ]) 42) ⊑ (((Λ X. λ x : X. x) [★]) 42)`

Expected compiled pair at the initial checkpoint:

`(((Λ X. λ x. x) [ℕ]) (42 ⟨ idℕ ⟩))`
`⊑ (((Λ X. λ x. x) [★]) (42 ⟨ ℕ ! ⟩))`

Both executions allocate a representation for `X`.  Reduction exposes matched
active reveals and matched active conceals.

Status: green.  `MatchedInstantiation.agda` checks the source typings, source
imprecision, ordinary compiler outputs, and six checkpoints `C0` through `C5`.
There is one checkpoint after every left reduction; the right run takes one
allocation step, then stutters once, and then takes one step per checkpoint.
Every checkpoint has a live CTI derivation and a generated, pinned Imp Ladder.

The allocation world is

`⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩`.

All active conversion boundaries are paired.  Their rebase plan is the
identity, so this example validates the baseline where the world comparing
the representations `ℕ ⊑ ★` is also the world aligning `X` with `X'`.
It intentionally does not decide how those worlds differ in an alias case.

### 5. `SourceOnlyInstantiation.agda`

Source pair:

`(((Λ X. λ x : X. x) [ℕ]) 42) ⊑ ((λ x : ★. x) 42)`

Expected compiled pair at the initial checkpoint:

`(((Λ X. λ x. x) [ℕ]) (42 ⟨ idℕ ⟩))`
`⊑ ((λ x. x) (42 ⟨ ℕ ! ⟩))`

Only the left execution allocates a representation for `X`.  Reduction exposes
an active left-only reveal and conceal, and the right execution has no pivot at
that center.

### 6. `PolymorphicFunctionCast.agda`

Write `P = ∀ X. X ⇒ X` and `p = Λ X. λ x : X. x`.  The source pair is

`((λ f : P. f [ℕ] 42) p)`
`⊑ ((λ f : ★ ⇒ ★. f 42) p)`.

The right compilation casts `p` from the polymorphic function type `P` to the
monomorphic dynamic function type `★ ⇒ ★`, exercising `inst`.  This is
the isolated polymorphic function-cast example; both executions return `42`
(the right result is dynamic).

### 7. `Example12.agda`

Write `P = ∀ X. X ⇒ X`, `D = ★ ⇒ ★`, and
`p = Λ X. λ x : X. x`.  The checked source pair is

`((λ h : P. h [ℕ] 7) ((λ f : P. f) p))`
`⊑ ((λ h : P. h [ℕ] 7) ((λ f : D. f) p))`.

The annotated identity applications are the source-level `cast` idiom from
`Source.agda`.  The displays expand the helper so the programs remain
self-contained and human readable.

Both programs have source type `ℕ`, are related by gradual term
imprecision, and their ordinary compilations evaluate to `7`.  On the less
precise side the inner application inserts

`p ⟨ inst ((? X) ↦ (X !)) ⟩`

and the outer application inserts

`□ ⟨ gen ((X !) ↦ (? X)) ⟩`.

Thus this is an honest source-level driver for the `inst`/`gen` allocation
scenario in Example 12.

The original hand-written cast-calculus pair is

`(((Λ X. λ x : X. x) [ℕ]) 7)`
`⊑ (((((Λ X. λ x : X. x)`
`⟨ inst ((? X) ↦ (X !)) ⟩)`
`⟨ gen ((X !) ↦ (? X)) ⟩) [ℕ]) 7)`.

Those two literal terms are not ordinary compiler images or intermediate
states: the compiler also inserts the applications' argument casts, and
call-by-value takes `β-inst` before an administrative identity function can
expose the nested pre-allocation cast term.  The source example therefore gates
the same cast directions and final behavior without claiming equality to that
literal checkpoint.

`Example12.agda` checks the complete whole-program schedule C0--C15: C0 is the
compiler output, and C1--C15 follow the fifteen more-precise reductions one at
a time.  Every interval records the less-precise catch-up or stutter trace, and
both executions finish at `7`.  C0 has a closed live CTI derivation and a pinned
generated ladder.  C1 has a pinned generated obstruction ladder.  Its three
`?` cells isolate the missing boundary-state design: the source-only `Λ`
transition from a pending exact alias to an active focus, the active target
reveal for `α : ★`, and the nested active target reveal for `β : α`.

## Proposed additions

The latest rule audit identified two more examples that should follow the
initial seven, subject to agreement on their exact source terms:

- `NeutralReveal.agda`, using a polymorphic body of type `X ⇒ ★`, to
  expose an active domain conversion and a neutral result reveal;
- `NeutralConceal.agda`, using a higher-order body of type
  `(X ⇒ ★) ⇒ (X ⇒ ★)`, to make `β-conceal-⇒` expose a neutral
  result conceal.

The polymorphic K combinator gives two further families.  Write

`K₂ = Λ X. Λ Y. λ x : X. λ y : Y. x`,

`K₁ = Λ X. λ x : X. λ y : ★. x`, and

`K₀ = λ x : ★. λ y : ★. x`.

- `PolymorphicKPrecision.agda` should check the adjacent source pairs

  `K₂ [ℕ] [𝔹] 42 true ⊑ K₁ [ℕ] 42 true`

  and

  `K₁ [ℕ] 42 true ⊑ K₀ 42 true`.

  Removing one polymorphic binder at a time keeps the source-imprecision
  explanation local.  Every program is fully applied to data; the first two
  executions return `42 : ℕ`, while the fully dynamic result is tagged
  `42 : ★`.

- `PolymorphicKCast.agda` should use the same `K₂` value at three
  source-level ascriptions:

  `cast (∀ X. ∀ Y. X ⇒ Y ⇒ X) K₂`,

  `cast (∀ X. X ⇒ ★ ⇒ X) K₂`, and

  `cast (★ ⇒ ★ ⇒ ★) K₂`.

  Each ascribed value should then be instantiated as needed and applied to
  `42` and `true`.  We should retain only the adjacent pairs whose source
  typing and gradual imprecision check directly; the point is to exercise the
  compiler's polymorphic-to-function casts, not to assume transitivity in the
  example statement.
