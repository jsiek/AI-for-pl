LG-3r resister: frozen-trace prefix is not enough for generic unlift

Supervisor option (b) was tested at the structural-trace level.

The checked predicate shape is:

```agda
FrozenEmbedding k π
FrozenStructuralTraceᴿ k plan
```

At positive depth, `FrozenEmbedding (suc k) π` forces the center embedding
stored by a bind to have the constructor shape `keep π₀`.  The lifted trace
generator preserves this:

```agda
structural-lift-left-frozen :
  FrozenStructuralTraceᴿ k plan →
  FrozenStructuralTraceᴿ (suc k) (structural-lift-left plan X⊑★)
```

This confirms the intended local discipline for generated lifted traces:
target-store binds still allocate at target `Fin.zero`, while the center
embedding preserves the frozen source prefix by going behind it.

The result-level invariant requested for
`StructuralCatchupRightResult` does not thread cleanly through the existing
generic surface.

First, a field at depth `0` is vacuous:

```agda
frozen-trace-zero :
  (plan : StructuralWorldExtendᴿ χs W W′) →
  FrozenStructuralTraceᴿ zero plan
```

It records no information about the source-left slot and cannot exclude the
`skip` embedding from the LG-3q note.

Second, a positive-depth field cannot be added to the unindexed generic result
without changing the worker surface.  The needed depth is a property of the
ambient source-prefix discipline, not of an arbitrary `W`.

Third, even a positive-depth embedding predicate is still not the full plain
unlift witness.  In the bind case under
`liftWorldLeft X⊑★ W`, the predicate exposes `π = keep π₀`, but
`structural-Λ-replay` needs an outer trace

```agda
plan₀ : StructuralWorldExtendᴿ χs W W′
```

whose lifted trace is the child endpoint.  From an arbitrary

```agda
ins : TargetInsert wk↪ᵗ (keep π₀)
        (liftWorldLeft X⊑★ W) W₁
```

the current `TargetInsert` record gives pointwise geometry, but not the
unlifted insertion

```agda
ins₀ : TargetInsert wk↪ᵗ π₀ W W₁₀
```

nor an endpoint equality/transport showing

```agda
W₁ ≡ liftWorldLeft X⊑★ W₁₀
```

So a per-constructor embedding condition rules out the obvious `skip` case,
but it still does not reconstruct the exact outer plan required by replay.

There is also a concrete surface mismatch with the existing generic target
step:

```agda
TE.rightBindTargetInsert : TargetInsert wk↪ᵗ wk↪ᵗ W
  (rightOnlyWorld W B)
```

If that row is used at a lifted world, `wk↪ᵗ` is the `skip` embedding from
the LG-3q obstruction.  The F2-friendly route is the already checked
transported package path, where an outer target package is lifted by
`structural-lift-left`; that path has the positive-depth frozen proof, but the
generic result type does not remember that it came from this generator.

Conclusion:

- No CTI relation or reduction rule needs to change.
- The local frozen-prefix predicate and lifted preservation lemma check.
- The plain unlift still needs a refined/generated trace carrying the
  unlifted insertion and endpoint shape, or a replay/unlift field scoped to the
  result family that needs F2.
- The smart-comma route should keep using the hereditary replay pattern unless
  a refined smart trace is introduced; window inversion should not be forced.

Stopped per the F2 resister rule.

2026-08-17 LG-3s postscript:

The supervisor ruling to use hereditary replay/unlift fields was tested at the
field-shape level.  The one-layer plain field can be stated with heterogeneous
equalities:

```agda
source-Λ-left-unlift :
  {W₀ : World Δ₀ Δᴿ Δᵒ}
  {γ₀ : CtxImp W₀}
  {γᴸ : CtxImp (liftWorldLeft X⊑★ W₀)}
  {U : Term (suc Δ₀)}
  {p₀ : A₀ ⊑ᵂ⟨ liftWorldLeft X⊑★ W₀ ⟩ B₀}
  {q₀ : `∀ A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
  → W ≅ liftWorldLeft X⊑★ W₀
  → γ ≅ γᴸ
  → M ≅ U
  → q ≅ p₀
  → NonVar A₀
  → zero ∈ᵗ A₀
  → LiftCtxᴸ X⊑★ γ₀ γᴸ
  → Value U
  → ...
```

The smart shape similarly uses:

```agda
liftW : SmartCommaLiftᴸ W₀ Wᵐ
liftγ : SmartLiftCtxᴸ γ₀ γᵐ
W ≅ Wᵐ
γ ≅ γᵐ
```

Those equalities solve the generic-index statement problem.  They do not solve
the hereditary result problem.

If the field returns a full `StructuralCatchupRightResult`, the result record
becomes recursive:

```agda
record StructuralCatchupRightResult ... where
  field
    source-Λ-left-unlift : ... → StructuralCatchupRightResult ...
    source-Λ-smart-unlift : ... → StructuralCatchupRightResult ...
```

Concrete generators such as `structural-catchup-refl` would then need to build
a result whose unlift field builds another result with another unlift field.
The obvious definition is an unguarded self-call and fails termination.  Making
the result coinductive would be a broad change to the internal proof object,
not a local hereditary-field addition.

If the field instead returns a nonrecursive payload containing only the
endpoint trace, final value, reduction, final relation, and conceal-partner
fields, a single source-Λ row closes but nested source lambdas do not.  In:

```agda
Λ (Λ V)
```

the inner source-Λ row produces a catchup result at
`liftWorldLeft X⊑★ W`.  The outer row then needs to unlift that inner result's
trace one more layer.  A one-layer payload has forgotten the hereditary unlift
capability, so the proof is back at the LG-3q obstruction:

```agda
planᵇ : StructuralWorldExtendᴿ χs (liftWorldLeft X⊑★ W) Wᵇ
```

while `structural-Λ-replay` needs:

```agda
plan₀ : StructuralWorldExtendᴿ χs W W′
```

with the endpoint relation under `liftWorldLeft X⊑★ W′`.

The exact missing datum is therefore a finite, stack-polymorphic hereditary
source-Λ replay certificate, not a one-step field:

```agda
SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q

source-Λ-stack-unlift :
  SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → StructuralCatchupRightPayload W₀ γ₀ M₀ M″ q₀
```

The stack needs a base constructor plus plain and smart source-Λ frames carrying
the corresponding lift/context/value/type-side replay data.  Source-Λ rows
would extend the caller's stack and delegate to the premise field, making
nested `Λ` finite and nonrecursive.  Target bind rows must carry the generated
commutation once: a `rightBindTargetInsert` at a lifted/smart world unlifts to
the same target bind at the stack's outer world, with lifted or smart endpoint
evidence obtained by replaying the stack over the bind.

No CTI relation, imprecision relation, or reduction rule needs to change.  The
remaining blocker is this stack-polymorphic certificate and its per-row
generators.
