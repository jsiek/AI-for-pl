module proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootProof where

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
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; source-nu-index
  )
open import proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootDef using
  (WorldCoherentSourceKeepBlameRootᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using (world-coherent-source-one-step-indexed)


world-coherent-source-keep-blame-root-proofᵀ :
  WorldCoherentSourceKeepBlameRootᵀ
world-coherent-source-keep-blame-root-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {M = M} {M′ = M′} {A = A} {B = B}
    {ρ⁺ = ρ⁺} {p = p}
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ M→blame =
  world-coherent-source-one-step-indexed
    indexed lineage refl refl coherent exclusive unique
  where
  blame-relation = blame⊑ᵀ M′⊢

  result =
    weak-step-result
      (keep ∷ []) [] blame M′ Φ Δᴸ Δᴿ refl refl ρ⁺ A B refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      (λ safe occ q → source-nu-index safe occ q refl)
      p
      (↠-step M→blame ↠-refl)
      ↠-refl
      refl
      refl
      blame-relation

  transport =
    weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  indexed =
    weak-indexed-result result blame-relation transport type-coherence

  lineage =
    weak-step-store-lineage ρ⁺ rel-store-embedding-reflⁱ prefix-reflⁱ
