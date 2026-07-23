module
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupProof
  where

-- File Charter:
--   * Derives paired universal-conversion target closing from the fused
--     post-`β-∀•` semantic capability.
--   * Owns only the lifted administrative source keep step and delegates its
--     prepending to the shared world-coherent catch-up operation.
--   * Contains no semantic dispatcher, postulate, or permissive option.

open import Coercions using (`∀)
open import Data.Nat using (suc)
open import NuReduction using
  ( keep
  ; pure-step
  ; ξ-⟨⟩
  ; β-∀•
  ; _—→[_]_
  )
open import NuTerms using (Value; ⇑ᵗᵐ; _•; _⟨_⟩)
open import Relation.Binary.PropositionalEquality using (subst)
open import proof.Core.Properties.CoercionProperties using (open0-ext-suc-cancelᶜ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep using
  (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupDef
  using
    (WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionTargetClosingCatchupDef
  using (WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ)
open import proof.Core.Properties.NuTermProperties using (renameᵗᵐ-preserves-Value)


post-allocation-β-∀-cast :
  ∀ {V c s} →
  Value V →
  ((⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •) ⟨ s ⟩ —→[ keep ]
    (((⇑ᵗᵐ V) •) ⟨ c ⟩) ⟨ s ⟩
post-allocation-β-∀-cast {V = V} {c = c} vV =
  ξ-⟨⟩
    (subst
      (λ d → (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) • —→[ keep ]
        ((⇑ᵗᵐ V) •) ⟨ d ⟩)
      (open0-ext-suc-cancelᶜ c)
      (pure-step (β-∀• (renameᵗᵐ-preserves-Value suc vV))))


world-coherent-source-ν-paired-all-conversion-target-closing-catchup-proofᵀ :
  WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-conversion-target-closing-catchup-proofᵀ
    post-beta coherent exclusive wfL hA h⇑A s↑ liftν lift∀
    vV noV vV′ noV′ conversion V⊑V′ =
  world-coherent-left-catchup-prepend-keep-step
    (post-allocation-β-∀-cast vV)
    (post-beta coherent exclusive wfL hA h⇑A s↑ liftν lift∀
      vV noV vV′ noV′ conversion V⊑V′)
