module proof.DGG.Catchup.StructuralRightParkedEvolveProof where

-- File Charter:
--   * Embeds structural right-world extension traces into parked evolution.
--   * Uses the retained target insertion and singleton target-store equation
--     at every structural bind.

open import Reduction using (StoreChanges; []; _∷_; keep)
import proof.DGG.CtxImp as CTI2
open import proof.DGG.Parked.ParkedWorldDef using
  ( ParkedEvolve
  ; ParkedWorld
  ; evolve-keepᴿ
  ; evolve-refl
  ; evolve-structural-right-bind
  ; parked-structural-right-insert
  )
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  ( StructuralWorldExtendᴿ
  ; structural-[]
  ; structural-bind
  ; structural-keep
  )


StructuralRightParkedEvolveᵀ : Set₁
StructuralRightParkedEvolveᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → ParkedWorld W
  → StructuralWorldExtendᴿ χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′


structural-right-parked-evolve : StructuralRightParkedEvolveᵀ
structural-right-parked-evolve parked structural-[] = evolve-refl
structural-right-parked-evolve parked (structural-keep plan) =
  evolve-keepᴿ (structural-right-parked-evolve parked plan)
structural-right-parked-evolve parked
    (structural-bind ins follows plan) =
  evolve-structural-right-bind ins follows
    (structural-right-parked-evolve
      (parked-structural-right-insert parked ins follows) plan)
