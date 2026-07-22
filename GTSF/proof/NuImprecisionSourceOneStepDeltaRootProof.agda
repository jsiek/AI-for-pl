module proof.NuImprecisionSourceOneStepDeltaRootProof where

-- File Charter:
--   * Implements the synchronized source delta root for natural addition.
--   * Builds matching keep-step source and target tails to the same constant.
--   * Lifts the final constant relation through the ambient allocation prefix.
--   * Uses identity transport, coherence, and reflexive store lineage.
--   * Contains no postulate, hole, incomplete match, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_+_)

open import ImprecisionWf using (idι)
open import NuReduction using
  (δ-⊕; keep; pure-step; ↠-refl; ↠-step)
open import NuTerms using ($; _⊕[_]_)
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; κ⊑κᵀ
  ; prefix-reflⁱ
  )
open import TermTyping using (⊢$)
open import Types using (`ℕ; ‵_)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionSourceOneStepDeltaRootDef using
  (WorldCoherentSourceDeltaRootᵀ)
open import
  proof.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepResultDef
  using (world-coherent-source-one-step-indexed)


world-coherent-source-delta-root-proofᵀ :
  WorldCoherentSourceDeltaRootᵀ
world-coherent-source-delta-root-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {m = m} {n = n}
    prefix coherent exclusive unique =
  world-coherent-source-one-step-indexed
    indexed transport type-coherence lineage refl refl coherent exclusive
    unique
  where
  result-typingᴸ =
    ⊢$ (κℕ (m + n))

  result-typingᴿ =
    ⊢$ (κℕ (m + n))

  related⁺ =
    allocation-prefixᵀ prefix κ⊑κᵀ result-typingᴸ result-typingᴿ

  δ-step =
    ↠-step (pure-step δ-⊕) ↠-refl

  result =
    weak-step-result
      (keep ∷ []) (keep ∷ [])
      ($ (κℕ (m + n))) ($ (κℕ (m + n)))
      Φ Δᴸ Δᴿ refl refl ρ⁺ (‵ `ℕ) (‵ `ℕ) refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      idι
      δ-step
      δ-step
      refl
      refl
      related⁺

  indexed =
    weak-indexed-result result related⁺

  transport =
    weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  lineage =
    weak-step-store-lineage ρ⁺ rel-store-embedding-reflⁱ prefix-reflⁱ
