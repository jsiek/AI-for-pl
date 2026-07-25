module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedWideningCatchupProof
  where

-- File Charter:
--   * Proves exact-world terminal catch-up for compatible paired widenings.
--   * Uses source inertness for the zero-step terminal case and the explicit
--     cross bridge for the source-widen/target-frame case.
--   * Takes only the source-widen handler contract and imports no source
--     runtime record or implementation.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import NuReduction using
  ( blame-⟨⟩
  ; pure-step
  )
open import NuTerms using
  ( no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  ( compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-target-typing
  ; paired-widening
  ; prefix-reflⁱ
  )
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  (left-catchup-indexed-prepend-keepᵀ)
open import proof.Catchup.Core.NuImprecisionCatchupPrefixSupport using
  ( left-catchup-indexed-prefix-blameᵀ
  ; left-catchup-indexed-prefix-valueᵀ
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames using
  (world-coherent-left-catchup-prefix-target-widen-castᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedWideningCatchupDef
  using (WorldCoherentFinalPairedWideningCatchupᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef using
  (WorldCoherentSourceWidenCatchupᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)


world-coherent-final-paired-widening-catchup-proofᵀ :
  WorldCoherentSourceWidenCatchupᵀ →
  WorldCoherentFinalPairedWideningCatchupᵀ
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen {p = p} {q = q}
    coherent exclusive wfL (inj₂ refl) vV′ noV′ inert-c′
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    source-comp target-comp compat W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prepend-keepᵀ
      (pure-step blame-⟨⟩)
      (left-catchup-indexed-prefix-blameᵀ
        prefix-reflⁱ (no•-⟨⟩ noV′)
        (blame⊑ᵀ target⊢)))
    (weak-step-store-lineage _ rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
  where
  target⊢ = nu-term-imprecision-target-typing
    (conv⊑convᵀ
      (paired-widening
        {p = p} {q = q}
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        source-comp target-comp compat)
      W⊑V′)
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′
    inert-c′ mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    source-comp target-comp
    (compatible-source-inert inert-c) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ inert-c ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ
        (paired-widening
          mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
          source-comp target-comp
          (compatible-source-inert inert-c))
        W⊑V′))
    (weak-step-store-lineage _ rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′
    inert-c′ mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    source-comp target-comp
    (compatible-target-inert-bridge bridge-evidence) W⊑V′
    with bridge-evidence inert-c′
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′
    inert-c′ mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    source-comp target-comp
    (compatible-target-inert-bridge bridge-evidence) W⊑V′
    | bridge , source-triangle , target-triangle =
  world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix-reflⁱ mode′ seal★′ c′⊑ c′-shape target-triangle
    source-catchup
  where
  initial =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no noW) vW noV′ W⊑V′)
      (weak-step-store-lineage _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive wfL

  source-catchup =
    source-widen prefix-reflⁱ mode seal★ c⊑
      vV′ noV′ initial bridge c-shape source-triangle
