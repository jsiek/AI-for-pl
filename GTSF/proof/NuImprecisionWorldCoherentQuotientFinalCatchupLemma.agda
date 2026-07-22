module
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupLemma
  where

-- File Charter:
--   * Assembles final quotient catch-up from the pre-existing plain
--     quotient-inst capability.
--   * Derives the eager inst/function-tag residual internally, showing that
--     the GenSafe repair introduces no additional semantic assumption.

open import
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupProof
  using (world-coherent-quotient-final-catchup-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientClassificationProof
  using (world-coherent-quotient-classification-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientInstCatchupDef
  using (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientInstFunTagCatchupLemma
  using (world-coherent-quotient-inst-fun-tag-catchupᵀ)


world-coherent-quotient-final-catchupᵀ :
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentQuotientFinalCatchupᵀ
world-coherent-quotient-final-catchupᵀ plain =
  world-coherent-quotient-final-catchup-proofᵀ
    world-coherent-quotient-classification-proofᵀ
    plain (world-coherent-quotient-inst-fun-tag-catchupᵀ plain)
