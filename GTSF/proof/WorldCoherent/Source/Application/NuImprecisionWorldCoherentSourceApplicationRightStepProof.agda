module proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationRightStepProof where

-- File Charter:
--   * Proves the world-coherent source application-right frame capability.
--   * Builds the framed source step with `ξ-·₂` and delegates the full
--     simulation package to the ambient source one-step prefix contract.
--   * Contains no semantic dispatcher, postulate, hole, or permissive option.

open import NuReduction using (ξ-·₂)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


world-coherent-source-application-right-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceApplicationRightStepᵀ
world-coherent-source-application-right-step-proofᵀ
    prefix prefixρ coherent exclusive unique wfL wfR okVM okM′
    VM⊢ M′⊢ VM⊑M′ vV shiftV M→M₁ =
  prefix prefixρ coherent exclusive unique wfL wfR okVM okM′
    VM⊢ M′⊢ VM⊑M′ (ξ-·₂ vV shiftV M→M₁)
