module proof.NuImprecisionWorldCoherentSourceKeepRelationProof where

-- File Charter:
--   * Builds an exact one-source-step result from a supplied final QTI
--     relation and one source `keep` step.
--   * Uses identity transport/coherence and reflexive store lineage.
--   * Contains no postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)

open import NuReduction using (keep; ↠-refl; ↠-step)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import proof.NuImprecisionWorldCoherentSourceKeepRelationDef using
  (WorldCoherentSourceKeepRelationᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (world-coherent-source-one-step-indexed)


world-coherent-source-keep-relation-proofᵀ :
  WorldCoherentSourceKeepRelationᵀ
world-coherent-source-keep-relation-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {M = M} {M′ = M′} {L = L} {A = A} {B = B} {p = p}
    coherent exclusive unique final-relation M→L =
  world-coherent-source-one-step-indexed
    indexed transport type-coherence lineage refl refl coherent exclusive
    unique
  where
  result =
    weak-step-result
      (keep ∷ []) [] L M′ Φ Δᴸ Δᴿ refl refl ρ A B refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      p
      (↠-step M→L ↠-refl)
      ↠-refl
      refl
      refl
      final-relation

  indexed =
    weak-indexed-result result final-relation

  transport =
    weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  lineage =
    weak-step-store-lineage ρ rel-store-embedding-reflⁱ prefix-reflⁱ
