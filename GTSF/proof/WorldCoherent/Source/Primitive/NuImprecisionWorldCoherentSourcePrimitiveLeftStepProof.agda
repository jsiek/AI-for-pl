module proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveLeftStepProof where

-- File Charter:
--   * Proves the world-coherent source primitive-left frame capability.
--   * Builds the framed primitive source step with `ξ-⊕₁` and delegates
--     simulation obligation to the ambient source one-step prefix contract.
--   * Contains no semantic dispatcher, postulate, hole, or permissive option.

open import NuReduction using (ξ-⊕₁)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)


world-coherent-source-primitive-left-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ
world-coherent-source-primitive-left-step-proofᵀ
    prefix prefixρ coherent exclusive unique wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ L→L′ shiftM =
  prefix prefixρ coherent exclusive unique wfL wfR okLM okM′
    LM⊢ M′⊢ LM⊑M′ (ξ-⊕₁ L→L′ shiftM)
