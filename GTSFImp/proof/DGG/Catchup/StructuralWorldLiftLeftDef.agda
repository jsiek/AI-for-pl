module proof.DGG.Catchup.StructuralWorldLiftLeftDef where

-- File Charter:
--   * States structural extension under the canonical source-left lift.
--   * Retains every target insertion for ordinary source-Λ recursion.

open import Reduction using (StoreChanges)
open import Imprecision using (VarImp)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralWorldExtendDef


record StructuralLiftLeftResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    (v : VarImp) : Set₁ where
  field
    premise-plan : StructuralWorldExtendᴿ χs
      (CTI2.liftWorldLeft v W) (CTI2.liftWorldLeft v W′)
