module
  proof.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupProof
  where

-- File Charter:
--   * Assembles direct paired universal target closing by the two constructors
--     of `PairedCast`.
--   * Delegates conversion and widening semantics to whole strict theorem
--     capabilities.
--   * Contains no semantic leaf implementation or permissive option.

open import QuotientedTermImprecision using
  (paired-conversion; paired-widening)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupDef
  using
    (WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllTargetClosingCatchupDef
  using (WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllWideningTargetClosingCatchupDef
  using
    (WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ)


world-coherent-source-ν-paired-all-target-closing-catchup-proofᵀ :
  WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-target-closing-catchup-proofᵀ
    conversion-catchup widening-catchup
    coherent exclusive wfL hA h⇑A s↑ liftρν liftρ∀
    vV noV vV′ noV′ (paired-conversion conversion) V⊑V′ =
  conversion-catchup coherent exclusive wfL hA h⇑A s↑ liftρν liftρ∀
    vV noV vV′ noV′ conversion V⊑V′
world-coherent-source-ν-paired-all-target-closing-catchup-proofᵀ
    conversion-catchup widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A s↑ liftρν liftρ∀
    vV noV vV′ noV′
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat)
    V⊑V′ =
  widening-catchup {q = q}
    coherent exclusive wfL hA h⇑A s↑ liftρν liftρ∀
    vV noV vV′ noV′ mode seal★ c⊑ mode′ seal★′ c′⊑ compat
    V⊑V′
