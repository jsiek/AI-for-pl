module proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepProof where

-- File Charter:
--   * Proves the world-coherent source primitive-right frame capability.
--   * Builds the framed primitive source step with `ξ-⊕₂` and delegates the
--     simulation obligation to the ambient source one-step prefix contract.
--   * Contains no semantic dispatcher, postulate, hole, or permissive option.

open import NuReduction using (ξ-⊕₂)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)


world-coherent-source-primitive-right-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ
world-coherent-source-primitive-right-step-proofᵀ
    prefix prefixρ coherent exclusive wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ vL shiftL M→M₁ =
  prefix prefixρ coherent exclusive wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ (ξ-⊕₂ vL shiftL M→M₁)
