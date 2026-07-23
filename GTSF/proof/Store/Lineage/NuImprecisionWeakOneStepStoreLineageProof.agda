module proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof where

-- File Charter:
--   * Composes weak-result relational-store lineage across left-silent
--     resumption.
--   * Uses only focused relational-store embedding algebra and the stable
--     result-composition constructor.
--   * Contains no recursive catch-up, allocation, or dispatcher proof.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)

open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-prepend-left-silentᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentResult
  ; WeakOneStepResult
  ; left-silent
  ; left-silent-invariant
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; silentResult
  ; sourceChanges
  ; sourceResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import proof.Core.Properties.ReductionProperties using (applyTyVars-++)


weak-one-step-prepend-left-silent-store-lineageᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B ρ}
    (silent : LeftSilentResult
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ}) →
  let first = silentResult silent in
  ∀ {χ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ) →
  WeakOneStepStoreLineage first →
  WeakOneStepStoreLineage second →
  WeakOneStepStoreLineage
    (weak-one-step-prepend-left-silentᵀ silent second)
weak-one-step-prepend-left-silent-store-lineageᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-step-store-lineage store₁ embedding₁ prefix₁)
    (weak-step-store-lineage store₂ embedding₂ prefix₂)
    with rel-store-embedding-prefix-invⁱ prefix₁ embedding₂
weak-one-step-prepend-left-silent-store-lineageᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-step-store-lineage store₁ embedding₁ prefix₁)
    (weak-step-store-lineage store₂ embedding₂ prefix₂)
    | store₁₂ , embedding₁₂ , prefix₁₂ =
  weak-step-store-lineage store₁₂
    (rel-store-embedding-congⁱ
      (λ α → sym
        (applyTyVars-++
          (sourceChanges first) (sourceChanges second) α))
      (λ β → refl)
      (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
    (store-imp-prefix-transⁱ prefix₁₂ prefix₂)
