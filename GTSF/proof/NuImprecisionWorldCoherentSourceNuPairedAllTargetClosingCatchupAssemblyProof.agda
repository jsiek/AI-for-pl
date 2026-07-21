module
  proof.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupAssemblyProof
  where

-- File Charter:
--   * Connects the structural paired-conversion target-closing architecture
--     and the independent paired-widening target-closing capability to the
--     whole direct paired-cast target-closing theorem.
--   * Exposes every remaining semantic dependency in the exact consumer type.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import QuotientedTermImprecision using
  (paired-conversion; paired-widening)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  using (PairedLambdaTargetClosingContinuationHandlers)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupProof
  using
  (world-coherent-source-ν-paired-all-conversion-target-closing-catchup-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupAssemblyProof
  using
  (world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupDef
  using (WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllWideningTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationHandlers →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ
    handlers value-catchup unseal-catchup
    widening-catchup coherent exclusive wfL hA h⇑A reveal
    liftν lift∀ vV noV vV′ noV′
    (paired-conversion conversion) V⊑V′ =
  conversion-catchup coherent exclusive wfL hA h⇑A reveal
    liftν lift∀ vV noV vV′ noV′ conversion V⊑V′
  where
  conversion-catchup :
    WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ
  conversion-catchup =
    world-coherent-source-ν-paired-all-conversion-target-closing-catchup-proofᵀ
      (world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ
        handlers value-catchup unseal-catchup)
world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ
    handlers value-catchup unseal-catchup
    widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A reveal liftν lift∀
    vV noV vV′ noV′
    (paired-widening mode seal c⊑ mode′ seal′ c′⊑ compatible)
    V⊑V′ =
  widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A reveal liftν lift∀
    vV noV vV′ noV′ mode seal c⊑ mode′ seal′ c′⊑ compatible
    V⊑V′
