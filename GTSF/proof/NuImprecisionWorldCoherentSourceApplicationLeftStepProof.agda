module proof.NuImprecisionWorldCoherentSourceApplicationLeftStepProof where

-- File Charter:
--   * Proves the world-coherent source application-left frame capability.
--   * Builds the framed application source step with `ξ-·₁` and delegates the
--     simulation obligation to the ambient source one-step prefix contract.
--   * Contains no semantic dispatcher, postulate, hole, or permissive option.

open import NuReduction using (ξ-·₁)
open import proof.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


world-coherent-source-application-left-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ
world-coherent-source-application-left-step-proofᵀ
    prefix prefixρ coherent exclusive wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ L→L′ shiftM =
  prefix prefixρ coherent exclusive wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ (ξ-·₁ L→L′ shiftM)
