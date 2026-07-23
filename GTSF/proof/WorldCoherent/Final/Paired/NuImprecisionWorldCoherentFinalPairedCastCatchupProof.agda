module proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastCatchupProof
  where

-- File Charter:
--   * Assembles exact-world terminal paired-cast catch-up by the two
--     constructors of PairedCast.
--   * Leaves conversion cancellation and paired widening/allocation as
--     explicit whole semantic dependencies.
--   * Imports no recursive source-runtime or value-catch-up dispatcher.

open import QuotientedTermImprecision using
  (paired-conversion; paired-widening)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastCatchupDef using
  (WorldCoherentFinalPairedCastCatchupᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedConversionCatchupDef using
  (WorldCoherentFinalPairedConversionCatchupᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedWideningCatchupDef using
  (WorldCoherentFinalPairedWideningCatchupᵀ)


world-coherent-final-paired-cast-catchup-proofᵀ :
  WorldCoherentFinalPairedConversionCatchupᵀ →
  WorldCoherentFinalPairedWideningCatchupᵀ →
  WorldCoherentFinalPairedCastCatchupᵀ
world-coherent-final-paired-cast-catchup-proofᵀ
    conversion-catchup widening-catchup
    coherent exclusive wfL final vV′ noV′ inert-c′
    (paired-conversion conversion) W⊑V′ =
  conversion-catchup coherent exclusive wfL final
    vV′ noV′ inert-c′ conversion W⊑V′
world-coherent-final-paired-cast-catchup-proofᵀ
    conversion-catchup widening-catchup
    coherent exclusive wfL final vV′ noV′ inert-c′
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat) W⊑V′ =
  widening-catchup coherent exclusive wfL final
    vV′ noV′ inert-c′ mode seal★ c⊑ mode′ seal★′ c′⊑
    compat W⊑V′
