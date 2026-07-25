module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Implements exact-final paired-conversion catch-up from a source value
--     while retaining one independent runtime sibling.
--   * Splits reveal and conceal from paired widening so dependent hereditary
--     replacement patterns elaborate in their own constructor family.
--   * Contains no paired-widening dependency, postulate, hole, or permissive
--     option.

open import Coercions using
  ( Inert
  ; seal
  ; _↦_
  ; `∀
  )
open import Conversion using
  ( RevealConversion
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (β-id; pure-step)
open import NuTerms using
  ( no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; prefix-reflⁱ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Types using (＇_; _⇒_; `∀)
open import
  proof.Core.Properties.NuImprecisionPairedReplacementProjection
  using (paired-replacement-same-source→right)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixSupport
  using (left-catchup-indexed-prefix-valueᵀ)
open import
  proof.Quotient.NuImprecisionQuotientValue
  using (left-catchup-indexed-one-keep-valueᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-coherent-left-indexed-catchup)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupDef
  using
  (WorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupᵀ)


source-unseal-target-inert-sibling-impossible :
  ∀ {Φ Δᴸ Δᴿ μ Σ α β X c′ A′ B′} →
  Inert c′ →
  RevealConversion μ Δᴿ Σ β X c′ A′ B′ →
  Φ ∣ Δᴸ ⊢ ＇ α ⊑ A′ ⊣ Δᴿ →
  ⊥
source-unseal-target-inert-sibling-impossible
    () (reveal-id-var hY ok) p
source-unseal-target-inert-sibling-impossible
    () reveal-id-base p
source-unseal-target-inert-sibling-impossible
    () reveal-id-★ p
source-unseal-target-inert-sibling-impossible
    () (reveal-unseal hX β∈Σ ok) p
source-unseal-target-inert-sibling-impossible
    inert (reveal-fun s↓ t↑) ()
source-unseal-target-inert-sibling-impossible
    inert (reveal-all s↑) ()


world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ :
  WorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupᵀ
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-reveal corr (reveal-id-var hY ok) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↑ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-reveal corr reveal-id-base target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↑ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-reveal corr reveal-id-★ target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↑ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    {p = p} coherent exclusive unique wfL
    vW noW vV′ noV′ inert-c′
    (paired-reveal corr
      (reveal-unseal hX α∈Σ ok) target replacement)
    W⊑V′ noR okR′ sibling =
  ⊥-elim
    (source-unseal-target-inert-sibling-impossible
      inert-c′ target p)
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    conversion@(paired-reveal
      corr (reveal-fun s↓ t↑) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ _ ↦ _ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    conversion@(paired-reveal
      corr (reveal-all s↑) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ `∀ _ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-conceal corr (conceal-id-var hY ok) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↓ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-conceal corr conceal-id-base target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↓ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    (paired-conceal corr conceal-id-★ target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-id vW)) vW noW
        (⊑conv↓ᵀ target W⊑V′ _
          (paired-replacement-same-source→right replacement)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    conversion@(paired-conceal
      corr (conceal-seal hX α∈Σ ok) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ seal _ _ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    conversion@(paired-conceal
      corr (conceal-fun s↑ t↓) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ _ ↦ _ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
    coherent exclusive unique wfL vW noW vV′ noV′ inert-c′
    conversion@(paired-conceal
      corr (conceal-all s↓) target replacement)
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ `∀ _ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
