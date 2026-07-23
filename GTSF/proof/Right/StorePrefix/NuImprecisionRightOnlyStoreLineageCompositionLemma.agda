module
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionLemma
  where

-- File Charter:
--   * Exposes canonical target-only weak-step lineage composition.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionDef
  using (WeakOneStepRightOnlyStoreLineageCompositionᵀ)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionProof
  using
  (weak-one-step-right-only-store-lineage-composition-proofᵀ)


weak-one-step-right-only-store-lineage-compositionᵀ :
  WeakOneStepRightOnlyStoreLineageCompositionᵀ
weak-one-step-right-only-store-lineage-compositionᵀ =
  weak-one-step-right-only-store-lineage-composition-proofᵀ
