module proof.NuImprecisionSourceOneStepBlameRootProof where

-- File Charter:
--   * Implements the ambient-prefix source keep-step blame root.
--   * Builds the exact source one-step result from the supplied keep step and
--     the refined target typing at the ambient relational store.
--   * Uses identity transport, identity type coherence, and reflexive
--     relational-store lineage at the final world.
--   * Contains no postulate, hole, incomplete match, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)

open import NuReduction using (keep; ↠-refl; ↠-step)
open import NuTerms using (blame)
open import QuotientedTermImprecision using (blame⊑ᵀ; prefix-reflⁱ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionSourceOneStepBlameRootDef using
  (WorldCoherentSourceKeepBlameRootᵀ)
open import
  proof.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepResultDef
  using (world-coherent-source-one-step-indexed)


world-coherent-source-keep-blame-root-proofᵀ :
  WorldCoherentSourceKeepBlameRootᵀ
world-coherent-source-keep-blame-root-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {M = M} {M′ = M′} {A = A} {B = B}
    {ρ⁺ = ρ⁺} {p = p}
    prefix coherent exclusive wfL wfR okM okM′ M⊢ M′⊢ M⊑M′ M→blame =
  world-coherent-source-one-step-indexed
    indexed transport type-coherence lineage refl refl coherent exclusive
  where
  blame-relation = blame⊑ᵀ M′⊢

  result =
    weak-step-result
      (keep ∷ []) [] blame M′ Φ Δᴸ Δᴿ refl refl ρ⁺ A B refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      p
      (↠-step M→blame ↠-refl)
      ↠-refl
      refl
      refl
      blame-relation

  indexed =
    weak-indexed-result result blame-relation

  transport =
    weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  lineage =
    weak-step-store-lineage ρ⁺ rel-store-embedding-reflⁱ prefix-reflⁱ
