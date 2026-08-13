module proof.DGG.Catchup.StructuralWorldLiftLeftProof where

-- File Charter:
--   * Lifts a structural target-extension trace under a source binder.
--   * Uses the canonical lifted target insertion at every bind.

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open import Imprecision using (VarImp)
open import Reduction using (StoreChanges)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldLiftLeftDef


structural-lift-left : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (v : VarImp)
  → StructuralLiftLeftResult plan v
structural-lift-left structural-[] v = record
  { premise-plan = structural-[] }
structural-lift-left (structural-keep plan) v
    with structural-lift-left plan v
structural-lift-left (structural-keep plan) v
    | record { premise-plan = planᴸ } =
  record { premise-plan = structural-keep planᴸ }
structural-lift-left (structural-bind ins follows plan) v
    with structural-lift-left plan v
structural-lift-left (structural-bind ins follows plan) v
    | record { premise-plan = planᴸ } =
  record
    { premise-plan = structural-bind
        (TE.liftLeftTargetInsert {v = v} ins) follows planᴸ
    }
