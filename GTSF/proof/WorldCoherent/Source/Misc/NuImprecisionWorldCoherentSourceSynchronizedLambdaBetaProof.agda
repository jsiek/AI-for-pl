module
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaProof
  where

-- File Charter:
--   * Proves synchronized ordinary-lambda beta from quotiented substitution.
--   * Takes one source and one target keep step, then relates both substituted
--     bodies at the unchanged coherent world.
--   * Preserves identity transport, type coherence, lineage, and world facts.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)

open import NuReduction using (keep; pure-step; β; ↠-refl; ↠-step)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; source-nu-index
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Substitution.Term.NuImprecisionTermSubstitutionDef using
  (QuotientedTermSubstitutionᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using (world-coherent-source-one-step-indexed)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-synchronized-lambda-beta-proofᵀ :
  QuotientedTermSubstitutionᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ
world-coherent-source-synchronized-lambda-beta-proofᵀ
    substitute coherent exclusive unique vV noV vV′ noV′ noN noN′
    body argument =
  world-coherent-source-one-step-indexed
    indexed lineage refl refl coherent exclusive
    unique
  where
  post-beta =
    substitute unique noN noN′ noV noV′ body argument

  result =
    weak-step-result
      (keep ∷ []) (keep ∷ []) _ _ _ _ _ refl refl _ _ _ refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      (λ safe occ q → source-nu-index safe occ q refl)
      _
      (↠-step (pure-step (β vV)) ↠-refl)
      (↠-step (pure-step (β vV′)) ↠-refl)
      refl
      refl
      post-beta

  transport = weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  indexed = weak-indexed-result result post-beta transport type-coherence

  lineage =
    weak-step-store-lineage _ rel-store-embedding-reflⁱ prefix-reflⁱ
