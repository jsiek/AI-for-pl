module proof.NuImprecisionWorldCoherentSourceOneStepCasesDef where

-- File Charter:
--   * Aggregates the nine named source-reduction case capabilities consumed
--     by the exact source one-step dispatcher.
--   * Refers to one independently checkable semantic boundary per reduction
--     family while preserving the dispatcher's canonical field names.
--   * Contains no case statement, implementation, postulate, hole,
--     permissive option, or broad simulation import.

open import proof.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuBlameStepDef using
  (WorldCoherentSourceNuBlameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import proof.NuImprecisionWorldCoherentSourcePureStepCasesDef using
  (WorldCoherentSourcePureStepCases)


record WorldCoherentSourceOneStepCases : Set₁ where
  field
    sourcePureStepCases : WorldCoherentSourcePureStepCases
    sourceAllocationStepCase : WorldCoherentSourceAllocationStepᵀ
    sourceApplicationLeftStepCase : WorldCoherentSourceApplicationLeftStepᵀ
    sourceApplicationRightStepCase :
      WorldCoherentSourceApplicationRightStepᵀ
    sourceCastFrameStepCase : WorldCoherentSourceCastFrameStepᵀ
    sourceNuFrameStepCase : WorldCoherentSourceNuFrameStepᵀ
    sourceNuBlameStepCase : WorldCoherentSourceNuBlameStepᵀ
    sourcePrimitiveLeftStepCase : WorldCoherentSourcePrimitiveLeftStepᵀ
    sourcePrimitiveRightStepCase : WorldCoherentSourcePrimitiveRightStepᵀ

open WorldCoherentSourceOneStepCases public
