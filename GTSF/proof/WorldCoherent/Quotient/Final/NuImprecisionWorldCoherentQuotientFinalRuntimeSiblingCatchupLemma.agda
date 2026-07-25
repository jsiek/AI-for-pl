module
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupLemma
  where

-- File Charter:
--   * Assembles accumulated terminal quotient runtime-sibling catch-up from
--     the single remaining plain quotient-inst sibling leaf.
--   * Supplies the canonical classifier-based exact-final implementation and
--     derives the eager inst/function-tag path internally.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or compatibility wrapper.

open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupProof
  using
  (world-coherent-quotient-final-runtime-sibling-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupProof
  using
  (world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ)


world-coherent-quotient-final-runtime-sibling-catchupᵀ :
  WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ
world-coherent-quotient-final-runtime-sibling-catchupᵀ plain =
  world-coherent-quotient-final-runtime-sibling-catchup-proofᵀ
    (world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ
      plain)
