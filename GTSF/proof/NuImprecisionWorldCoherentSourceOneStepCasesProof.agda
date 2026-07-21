module
  proof.NuImprecisionWorldCoherentSourceOneStepCasesProof
  where

-- File Charter:
--   * Assembles every named source one-step family into the exact DGG-facing
--     case record.
--   * Threads right-value catch-up only to the source primitive pure roots;
--     all other unfinished semantic families remain explicit parameters.
--   * Contains no semantic leaf, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuBlameStepLemma using
  (world-coherent-source-ν-blame-stepᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  (WorldCoherentSourceOneStepCases)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePureStepCasesProof
  using (world-coherent-source-pure-step-cases-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
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
