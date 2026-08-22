# T11 meet point: structural right extension to parked evolution

Purpose: draft the evolution-conversion side of the
`CatchupToMorePrecise` meet point.  The bottom-up structural catchup
result exposes a right structural world-extension trace, while the
top-down surface requires a parked evolution witness.

## Before context

The top-down result in `CatchupToMorePreciseDef.agda` wants both
witnesses:

```agda
ParkedEvolve [] χsᴿ W W′ ×
StructuralWorldExtendᴿ χsᴿ W W′ ×
StructuralWorldExtendᴿ χsᴿ Wᵖ Wᵖ′ ×
(Wᵖ′ ∣ [] ⊢² V ⊑ V′ ∶ q)
```

The bottom-up structural result already keeps the trace needed for the
second component:

```agda
record StructuralCatchupRightResult ... where
  field
    χs : StoreChanges Δᴿ Δᴿ′
    W′ : World Δᴸ Δᴿ′ Δ′
    structural-ext : StructuralWorldExtendᴿ χs W W′
```

The public `ValueCatchupRightAt` should not be the adapter input for
this conversion, because it returns only the erased
`ECR.WorldExtendᴿ χs W W′`; the structural bind witnesses and rebase
history are gone.

## Insertion inventory

All structural right binds have a target-store bind at the fresh
target variable.  This is forced by
`StructuralWorldExtendᴿ.structural-bind`, whose premise is
`TE.TargetInsert wk↪ᵗ π W W₁` and whose store side follows
`applyStores (bind B ∷ [])`.

Direct base target allocations use the zero-centered right-only world:

```agda
rightBindTargetInsert :
  TargetInsert wk↪ᵗ wk↪ᵗ W (CTI2.rightOnlyWorld W B)

rightBindTargetWindowInsert = record
  { windowEmbedding = window-here
  ; window-zero = refl
  ; window-old = λ Z → refl
  }
```

The direct call sites are the target instantiation, target lambda,
target generalization, and target reveal/conceal conversion steps.
They all pass `TE.rightBindTargetInsert` to the shared structural
target-bind step.

However, the right-catchup stack also transports these plans through
source-side lambda replay.  The plain source-lambda replay case calls
`structural-lift-left plan X⊑★`, and that helper rebuilds each bind
with `TE.liftLeftTargetInsert`.  The target insertion equation for
that helper is:

```agda
liftLeft-target-insert ins X =
  cong Fin.suc (target-insert ins X)
```

The checked probe records the resulting center positions:

```agda
direct-right-bind-fresh-target-center : ...
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Fin.zero
      ≡ Fin.zero

lift-left-around-right-bind-fresh-target-center : ...
  → toRenameᵗ
      (CTI2.ηᴿʷ
        (CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W B)))
      Fin.zero
      ≡ Fin.suc Fin.zero

parked-right-bind-after-lift-left-fresh-target-center : ...
  → toRenameᵗ
      (CTI2.ηᴿʷ
        (CTI2.rightOnlyWorld (CTI2.liftWorldLeft X⊑★ W) B))
      Fin.zero
      ≡ Fin.zero
```

Verdict: not every target insertion used by the structural
right-catchup stack is at `Fin.zero` in the parked M2 sense.  Direct
right binds are zero-centered, but a direct right bind transported
under a source-only lift has the fresh target center at
`Fin.suc Fin.zero`.  The conversion therefore needs a parked-family
extension that accepts the structural target insertion evidence, not
just a discipline argument asserting zero-centered parked steps.

## Candidate after context

The adapter should consume the structural bottom-up result, not the
erased public result:

```agda
StructuralRightParkedEvolveᵀ : Set₁
StructuralRightParkedEvolveᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedWorld W
  → StructuralWorldExtendᴿ χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′
```

Under the current `ParkedEvolve`, the intended recursive proof fails
in the `structural-bind` case whenever the intermediate world is not
definitionally `CTI2.rightOnlyWorld W B`.  The required parked-family
extension is the following constructor shape, placed with
`ParkedEvolve`:

```agda
evolve-structural-right-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ₁ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges (suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
    {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.targetStoreʷ W₁ ≡
      applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
  → ParkedEvolve χsᴸ χsᴿ W₁ W′
  → ParkedEvolve χsᴸ (bind B ∷ χsᴿ) W W′
```

With that constructor, the embedding is a structural recursion over
the existing trace:

```agda
structural-right-parked-evolve :
  StructuralRightParkedEvolveᵀ
```

The weaker erased statement is not the right target:

```agda
WorldExtendᴿ→ParkedEvolveᴿᵀ : Set₁
WorldExtendᴿ→ParkedEvolveᴿᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedWorld W
  → ECR.WorldExtendᴿ χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′
```

It has too little information to reconstruct non-zero structural
insertions, and those insertions are genuinely used by source-lambda
replay in the current right-catchup stack.
