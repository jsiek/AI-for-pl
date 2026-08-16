module proof.DGG.Catchup.StructuralWorldTagRebaseDef where

-- File Charter:
--   * States structural extension transport through a source tag rebase.
--   * Tracks the target pivot through every target-side store change.

open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (TyVar)
open import Reduction using
  (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralWorldExtendDef public using
  (StructuralWorldExtendᴿ; mapPivotChanges; mapPivotChanges-++;
   mapVarChanges)


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
