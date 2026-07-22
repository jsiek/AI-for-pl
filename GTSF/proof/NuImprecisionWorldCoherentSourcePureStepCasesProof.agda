module
  proof.NuImprecisionWorldCoherentSourcePureStepCasesProof
  where

-- File Charter:
--   * Assembles the four source pure-root families into their DGG-facing
--     aggregate record.
--   * Supplies the completed primitive family from the right-value engine
--     while retaining the three unfinished major families as parameters.
--   * Contains no semantic leaf, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootLemma
  using (world-coherent-source-primitive-pure-rootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePureStepCasesDef
  using (WorldCoherentSourcePureStepCases)
open import
  proof.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
  using (WorldCoherentSourceRuntimeBulletPureRootᵀ)


world-coherent-source-pure-step-cases-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceApplicationPureRootᵀ →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourcePureStepCases
world-coherent-source-pure-step-cases-proofᵀ
    right-catchup application-root bullet-root cast-root =
  record
    { sourceApplicationPureRootCase = application-root
    ; sourceRuntimeBulletPureRootCase = bullet-root
    ; sourceCastPureRootCase = cast-root
    ; sourcePrimitivePureRootCase =
        world-coherent-source-primitive-pure-rootᵀ right-catchup
    }
