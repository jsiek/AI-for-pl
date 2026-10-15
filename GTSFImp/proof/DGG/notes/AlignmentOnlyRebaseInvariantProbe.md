# Alignment-only source rebases and direct invariants

The strict companion
`AlignmentOnlyRebaseInvariantProbe.agda` checks the smallest semantic payload
available at `TargetIdentityReveal` checkpoint 3 and a decisive obstruction to
using an empty open-frame scan as the premise of `directInvariantsᶜ`.

## Result

The alpha source rebase is justified by an actual paired reveal boundary.  At
the allocation world, the available evidence is exactly:

- the source and target reveal typings at source `X` and target `Y′`;
- equality of their generator positions;
- the post-update representation comparison `ℕ ⊑ ★`.

The last comparison must use `pivot-afterᵗ update`.  Before the update the
source and target pivots are deliberately not aligned, so writing the
comparison in the old world would state the wrong fact.

This payload is enough to authenticate that an alignment-only change is
demanded by a paired conversion.  It is not, and cannot be, evidence for the
current `DirectWorldInvariantsᶜ` record.

At checkpoint 3 the target cells are:

    beta  X′ ↦ Y′
    alpha Y′ ↦ ★

After the source allocation and alpha alignment, source `X` occupies target
alpha's center.  Target beta remains unmatched, but its direct store entry is
the now-matched variable alpha.  Therefore beta satisfies neither alternative
of `unmatchedTargetsDynamicᶜ`: its entry is not `★`, and its alias target is
not source-unoccupied.

The Agda probe proves both facts:

```agda
checkpoint₃-allocation-direct :
  DirectWorldInvariantsᶜ TIR.checkpoint₃-allocation-world

checkpoint₃-alpha-not-direct :
  DirectWorldInvariantsᶜ TIR.checkpoint₃-world → ⊥
```

Thus no consistent payload on the alignment-only constructor can prove
preservation of the existing four-field record for this trusted world.  The
stronger gate must remain absence of **all** source rebases, not merely absence
of open frames.

## Exact proposed live API

The role is indexed by the update so that the paired comparison can be stated
before constructing the recursive world node:

```agda
data AlignmentBoundaryᶜ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ))
    (update : PivotUpdateᵗ (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)) : Set where

  paired-reveal-alignmentᶜ : ∀ {A A′ B B′ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → marksᶜ γ ⊢
        renameᵗ (toRenameⁱ (pivot-afterᵗ update)) Rᴸ
          ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ γ)) Rᴿ
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ update

  paired-conceal-alignmentᶜ : ∀ {A A′ B B′ Rᴸ Rᴿ}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → marksᶜ γ ⊢
        renameᵗ (toRenameⁱ (pivot-afterᵗ update)) Rᴸ
          ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ γ)) Rᴿ
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ update

data SourceRebaseRoleᶜ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ))
    (update : PivotUpdateᵗ (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)) : Set where
  open-frameᶜ : SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
  alignment-onlyᶜ : AlignmentBoundaryᶜ γ Xᴸ Xᴿ update
    → SourceRebaseRoleᶜ γ Xᴸ Xᴿ update

rebase-source-changeᶜ : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → (Xᴸ : TyVar (Δᵉ Γᴸ))
  → (Xᴿ : TyVar (Δᵉ Γᴿ))
  → (update : PivotUpdateᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ))
  → SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
  → (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ
  → WorldChange γ Γᴸ Γᴿ
```

Only `open-frameᶜ` is recognized by the direct constructor of
`SourceRebaseᶜ`.  `openFramesᶜ` ignores `alignment-onlyᶜ` and pushes the
endpoint pair for `open-frameᶜ`.

Crucially, retain the existing independent measure:

```agda
sourceRebaseCountᶜ
  (γ ▹ᶜ rebase-source-changeᶜ Xᴸ Xᴿ update role represented) =
  suc (sourceRebaseCountᶜ γ)
```

`directInvariantsᶜ`, grounding, and the current simulation interfaces keep
their `sourceRebaseCountᶜ γ ≡ 0` premise.  The new frame scan is used only
for reveal/conceal balance; it does not replace that stronger premise.
