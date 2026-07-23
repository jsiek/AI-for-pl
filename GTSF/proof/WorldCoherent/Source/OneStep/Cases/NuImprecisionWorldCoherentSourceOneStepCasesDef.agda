module proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepCasesDef where

-- File Charter:
--   * Aggregates the nine named source-reduction case capabilities consumed
--     by the source one-step outcome dispatcher.
--   * Refers to one independently checkable semantic boundary per reduction
--     family while preserving the dispatcher's canonical field names.
--   * Contains no case statement, implementation, postulate, hole,
--     permissive option, or broad simulation import.

open import proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuBlameStepDef using
  (WorldCoherentSourceNuBlameStepᵀ)
open import proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePureStepCasesDef using
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
