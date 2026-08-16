module proof.DGG.Catchup.StructuralWorldTagRebaseDef where

-- File Charter:
--   * States structural extension transport through a source tag rebase.
--   * Tracks the target pivot through every target-side store change.

open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (TyVar)
open import Consistency using (toRenameᵗ; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind)
open import proof.Reduction using (_++χ_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef


mapPivotChanges : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivotChanges [] pivot = pivot
mapPivotChanges (keep ∷ χs) pivot = mapPivotChanges χs pivot
mapPivotChanges (bind A ∷ χs) pivot =
  mapPivotChanges χs (TE.mapPivot (toRenameᵗ wk↪ᵗ) pivot)


mapPivotChanges-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → (pivot : Maybe (TyVar Δ₀))
  → mapPivotChanges (χs ++χ ψs) pivot
      ≡ mapPivotChanges ψs (mapPivotChanges χs pivot)
mapPivotChanges-++ [] ψs pivot = refl
mapPivotChanges-++ (keep ∷ χs) ψs pivot =
  mapPivotChanges-++ χs ψs pivot
mapPivotChanges-++ (bind A ∷ χs) ψs pivot =
  mapPivotChanges-++ χs ψs (TE.mapPivot (toRenameᵗ wk↪ᵗ) pivot)


record StructuralTagRebaseAtᴸResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?) : Set₁ where
  field
    Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.TagRebaseAtᴸ Wᵖ′ W′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralTagRebaseAtᴸPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?) : Set₁ where
  field
    W′ : CTI2.World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.TagRebaseAtᴸ Wᵖ′ W′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′
