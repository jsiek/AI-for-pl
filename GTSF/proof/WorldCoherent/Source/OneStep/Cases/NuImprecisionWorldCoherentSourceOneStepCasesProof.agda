module
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepCasesProof
  where

-- File Charter:
--   * Assembles every named source one-step family into the DGG-facing
--     outcome case record.
--   * Threads right-value catch-up only to the source primitive pure roots;
--     all other unfinished semantic families remain explicit parameters.
--   * Contains no semantic leaf, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuBlameStepLemma using
  (world-coherent-source-ν-blame-stepᵀ)
open import proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  (WorldCoherentSourceOneStepCases)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePureStepCasesProof
  using (world-coherent-source-pure-step-cases-proofᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
  using (WorldCoherentSourceRuntimeBulletPureRootᵀ)


world-coherent-source-one-step-cases-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceApplicationPureRootᵀ →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourceAllocationStepᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ →
  WorldCoherentSourceApplicationRightStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ →
  WorldCoherentSourceOneStepCases
world-coherent-source-one-step-cases-proofᵀ
    right-catchup application-root bullet-root cast-root
    allocation-step application-left-step application-right-step
    cast-frame-step ν-frame-step primitive-left-step primitive-right-step =
  record
    { sourcePureStepCases =
        world-coherent-source-pure-step-cases-proofᵀ
          right-catchup application-root bullet-root cast-root
    ; sourceAllocationStepCase = allocation-step
    ; sourceApplicationLeftStepCase = application-left-step
    ; sourceApplicationRightStepCase = application-right-step
    ; sourceCastFrameStepCase = cast-frame-step
    ; sourceNuFrameStepCase = ν-frame-step
    ; sourceNuBlameStepCase = world-coherent-source-ν-blame-stepᵀ
    ; sourcePrimitiveLeftStepCase = primitive-left-step
    ; sourcePrimitiveRightStepCase = primitive-right-step
    }
