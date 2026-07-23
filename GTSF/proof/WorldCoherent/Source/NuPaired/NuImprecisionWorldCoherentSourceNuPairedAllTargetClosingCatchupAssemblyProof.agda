module
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupAssemblyProof
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
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupProof
  using
  (world-coherent-source-ν-paired-all-conversion-target-closing-catchup-proofᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupAssemblyProof
  using
  (world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupDef
  using (WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllWideningTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ
    terminal value-catchup unseal-catchup
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
        terminal value-catchup unseal-catchup)
world-coherent-source-ν-paired-all-target-closing-catchup-assembly-proofᵀ
    terminal value-catchup unseal-catchup
    widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A reveal liftν lift∀
    vV noV vV′ noV′
    (paired-widening mode seal c⊑ mode′ seal′ c′⊑ compatible)
    V⊑V′ =
  widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A reveal liftν lift∀
    vV noV vV′ noV′ mode seal c⊑ mode′ seal′ c′⊑ compatible
    V⊑V′
