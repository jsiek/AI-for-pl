module
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePureStepCasesProof
  where

-- File Charter:
--   * Assembles the four source pure-root families into their DGG-facing
--     aggregate record.
--   * Supplies the completed primitive family from the right-value engine
--     while retaining the three unfinished major families as parameters.
--   * Contains no semantic leaf, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootLemma
  using (world-coherent-source-primitive-pure-rootᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePureStepCasesDef
  using (WorldCoherentSourcePureStepCases)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
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
