module proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveRightStepProof where

-- File Charter:
--   * Proves the world-coherent source primitive-right frame capability.
--   * Builds the framed primitive source step with `ξ-⊕₂` and delegates
--     simulation obligation to the ambient source one-step prefix contract.
--   * Contains no semantic dispatcher, postulate, hole, or permissive option.

open import NuReduction using (ξ-⊕₂)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)


world-coherent-source-primitive-right-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ
world-coherent-source-primitive-right-step-proofᵀ
    prefix prefixρ coherent exclusive unique wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ vL shiftL M→M₁ =
  prefix prefixρ coherent exclusive unique wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ (ξ-⊕₂ vL shiftL M→M₁)
