{-# OPTIONS --safe #-}

module proof.DGG.CatchupToLessPreciseProof where

-- File Charter:
--   * Adapts the canonical fuel-indexed left value catch-up induction to the
--     public CatchupToLessPrecise surface.
--   * Chooses the structural source-cast budget directly from the input CTI
--     derivation.
--   * Depends on no parked-world, boundary, or residual-family interface.

open import proof.DGG.Catchup.LeftValueCatchupDef using
  (LeftValueCatchupAt)
open import proof.DGG.Catchup.LeftValueCatchupLemma using
  (source-cast-bound)
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)


module _
    (left-value-catchup : ∀ {fuel} → LeftValueCatchupAt fuel)
  where

  catchup-to-less-precise : CatchupToLessPrecise
  catchup-to-less-precise no-open-frames rel vV′ =
    left-value-catchup no-open-frames rel vV′ (source-cast-bound rel)
