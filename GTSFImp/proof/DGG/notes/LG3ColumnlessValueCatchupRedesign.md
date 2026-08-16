# LG-3 Columnless Value Catch-Up Redesign

## Live Statement Shape

`ValueCatchupRightAt fuel` no longer takes `Value M′`, a syntactic
`CastColumn`, or `applyColumn M′ κ`.

The checked statement consumes:

```agda
Value M
→ (rel : W ∣ γ ⊢² M ⊑ M″ ∶ q)
→ TargetCastBound fuel rel
→ Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
  Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
  Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
  Σ[ N′ ∈ Term Δᴿ′ ]
    (Value N′
      × (M″ —↠[ χs ] N′)
      × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))
```

`Value M′` is intentionally absent.  The target value/core shape is recovered
by induction on `rel`: structural CTI heads replay or descend, and target-cast
heads expose the cast layer directly.

## Fuel Bound

The chosen fuel form is a derivation-indexed target-cast bound:

```agda
TargetCastBound fuel rel
```

This predicate recursively inspects the CTI derivation.  Its target-cast
clauses are:

```agda
TargetCastBound fuel (cast⊑cast² c c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel

TargetCastBound fuel (⊑cast² c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel
```

Structural CTI heads recurse into their premise derivations, paired heads take
products of premise bounds, and non-cast leaves contribute `⊤`.

This keeps the proof’s primary induction on `rel` while preserving the fuel
restart points needed for generated casts: `ground-other-decreaseᵀ`,
`project-expand-decreaseᵀ`, and the instantiation allocation decreases still
justify calls through `FuelStepSurface.smaller-extra`/`smaller-inst`.

## Surface Cleanup

Removed from the live Agda surface:

- `CastColumn`
- `applyColumn`
- `columnSize`
- `mapColumn₁`
- `mapColumn`
- `liftReductionThroughColumnᵀ`
- `columnSize-mapᵀ`
- `proof.DGG.Catchup.ColumnSupportProof`

The surviving support lemmas now live in
`proof.DGG.Catchup.FuelSupportProof`.

## Remaining Resister

The column peel blocker is superseded.  The remaining proof blocker is the
structural multi-step target-cast worker in
`lg3-target-cast-multistep-worker-resister.red`.
