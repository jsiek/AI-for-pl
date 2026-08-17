module proof.DGG.Catchup.StructuralWorldSmartLiftDef where

-- File Charter:
--   * States structural extension transport through a source smart lift.
--   * Exposes the post-lift center, which fresh insertion computes by pushout.

open import Data.Nat using (suc)

open import Types using (TyCtx)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralWorldExtendDef


record StructuralSmartLiftᴸResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ) : Set₁ where
  field
    Δᵐ′ : TyCtx
    Wᵐ′ : CTI2.World (suc Δᴸ) Δᴿ′ Δᵐ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵐ Wᵐ′
    post-lift : CTI2.SmartCommaLiftᴸ W′ Wᵐ′
