module
  proof.NuImprecisionRightOnlyStoreLineageCompositionProof
  where

-- File Charter:
--   * Proves target-only store-lineage composition.
--   * Inverts the first target-only prefix through the second embedding, then
--     composes the resulting embeddings and prefixes.
--   * Contains no term simulation, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import Data.List using (_∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)

open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  )
open import proof.NuImprecisionRightOnlyStoreLineageCompositionDef
  using (WeakOneStepRightOnlyStoreLineageCompositionᵀ)
open import proof.NuImprecisionRightOnlyStorePrefix using
  (right-only-store-prefix)
open import proof.NuImprecisionRightOnlyStorePrefixAlgebra using
  ( rel-store-embedding-right-only-prefix-invⁱ
  ; right-only-store-prefix-transⁱ
  )
open import proof.NuImprecisionSimulationResultDef using
  (sourceChanges; targetTailChanges)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; weak-step-store-lineage
  )
open import proof.ReductionProperties using (applyTyVars-++)


weak-one-step-right-only-store-lineage-composition-proofᵀ :
  WeakOneStepRightOnlyStoreLineageCompositionᵀ
weak-one-step-right-only-store-lineage-composition-proofᵀ
    first target→ second first-lineage second-lineage
    first-prefix second-prefix
    with rel-store-embedding-right-only-prefix-invⁱ
      first-prefix (lineageEmbedding second-lineage)
weak-one-step-right-only-store-lineage-composition-proofᵀ
    {χ = χ} first {χ′ = χ′} target→ second
    first-lineage second-lineage first-prefix second-prefix
    | store₁₂ , embedding₁₂ , prefix₁₂ =
  weak-step-store-lineage
      store₁₂ combined-embedding
      (right-only-store-prefix combined-prefix) ,
  combined-prefix
  where
  combined-embedding =
    rel-store-embedding-congⁱ
      (λ α → sym
        (applyTyVars-++
          (sourceChanges first) (sourceChanges second) α))
      (λ β → sym
        (applyTyVars-++
          (χ ∷ targetTailChanges first)
          (χ′ ∷ targetTailChanges second) β))
      (rel-store-embedding-composeⁱ
        (lineageEmbedding first-lineage) embedding₁₂)

  combined-prefix =
    right-only-store-prefix-transⁱ prefix₁₂ second-prefix
