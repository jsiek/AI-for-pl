LG-3q F2 resister: source-left unlift for target-only child traces

The requested F2 pullback is blocked at the structural trace surface, before
the value worker rows:

```agda
StructuralCatchupRightResult
  (liftWorldLeft X⊑★ W) γᴸ V M″ p
```

should yield a result over the outer world `W`, with the target trace/stores
unchanged and the endpoint replayed by `Λ⊑²`.  The available replay theorem
has the opposite shape:

```agda
structural-Λ-replay
  : (plan : StructuralWorldExtendᴿ χs W W′)
  → ...
  → liftWorldLeft X⊑★ W′ ∣ ... ⊢² U ⊑ F ∶ ...
  → W′ ∣ ... ⊢² Λ U ⊑ F ∶ ...
```

It needs an outer `plan : StructuralWorldExtendᴿ χs W W′`.  A completed child
result only carries:

```agda
structural-ext :
  StructuralWorldExtendᴿ χs (liftWorldLeft X⊑★ W) Wᵇ
```

For a generic structural trace, `Wᵇ` need not be definitionally
`liftWorldLeft X⊑★ W′` for any outer endpoint.  The bind constructor stores an
arbitrary target insertion:

```agda
structural-bind :
  TargetInsert wk↪ᵗ π W₀ W₁
  → ...
  → StructuralWorldExtendᴿ (bind B ∷ χs) W₀ W′
```

When `W₀ = liftWorldLeft X⊑★ W`, the center embedding has type
`π : suc Δ ↪ᵗ Δ₁`.  Nothing in `TargetInsert` forces this embedding to be
`keep π₀`.  If it starts with `skip`, the fresh source-left center is moved away
from `zero`; the source insertion equation then records:

```agda
toRenameᵗ (ηᴸʷ W₁) zero
  ≡ toRenameᵗ π (toRenameᵗ (ηᴸʷ (liftWorldLeft X⊑★ W)) zero)
```

This is a valid target-only structural insertion, but the endpoint no longer
has the strict front-fresh shape required by `liftWorldLeft X⊑★ W′`.
`target-source-reflect` prevents target variables from occupying that source
slot; it does not recover a center complement or prove the slot stayed at
front `zero`.

The smart-comma form has the same issue plus the expected pushout obstruction.
To pull back through `SmartCommaLiftᴸ`, the proof would need a complement of
the pending source slot in the endpoint center and a reconstructed
`SmartFreshBehindGuard`/`SmartAliasMergeGuard`.  The current
`EmbeddingWindow`/pushout utilities construct and push windows forward; they
do not invert an arbitrary endpoint structural trace back to such a window.

This is not a CTI relation or reduction problem.  The relation may remain
unchanged.  The checked support likely needs a generated-trace invariant:
either a source-Λ replay/unlift field carried by
`StructuralCatchupRightResult`, or a narrower target-only result whose bind
constructors record the frozen/window discipline that `structural-lift-left`
and `structural-smart-liftᴸ` generate.

Per the F2 tripwire, this goal is stopped here.  F3 and F4 can continue
independently.

2026-08-16 LG-3r postscript:

Option (b) was tested with a checked frozen-prefix predicate on structural
traces.  The local generated-trace fact checks for `structural-lift-left`, but
the generic `StructuralCatchupRightResult` still cannot carry a useful
positive-depth invariant without a refined/generated trace or replay field.
See `lg3r-frozen-trace-unlift-resister.red`.
