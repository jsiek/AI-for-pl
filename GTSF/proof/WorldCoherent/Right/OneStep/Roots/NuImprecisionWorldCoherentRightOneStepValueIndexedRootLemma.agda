module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootLemma
  where

-- File Charter:
--   * Supplies canonical indexed target-step residualization to the generic
--     source-value one-step root.
--   * Leaves prefix-aware right-value catch-up as the sole semantic premise.
--   * Contains no implementation, dispatcher, recursion, postulate, hole,
--     permissive option, compatibility alias, or dependency wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootDef
  using (WorldCoherentRightOneStepValueIndexedRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootProof
  using (world-coherent-right-one-step-value-indexed-root-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualLemma
  using (world-coherent-right-target-indexed-step-residualᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)


world-coherent-right-one-step-value-indexed-rootᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepValueIndexedRootᵀ
world-coherent-right-one-step-value-indexed-rootᵀ
    catchup runtime-transport =
  world-coherent-right-one-step-value-indexed-root-proofᵀ
    catchup
    (world-coherent-right-target-indexed-step-residualᵀ
      runtime-transport)
