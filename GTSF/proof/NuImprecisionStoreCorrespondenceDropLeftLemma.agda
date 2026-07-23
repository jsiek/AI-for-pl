module
  proof.NuImprecisionStoreCorrespondenceDropLeftLemma
  where

-- File Charter:
--   * Exposes exact removal of a source-only store lift from relational-store
--     correspondence evidence.
--   * Keeps callers independent of the exhaustive structural worker.
--   * Contains no term relation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import
  proof.NuImprecisionStoreCorrespondenceDropLeftDef
  using (StoreCorrespondenceDropLeftᵀ)
open import
  proof.NuImprecisionStoreCorrespondenceDropLeftProof
  using (store-correspondence-drop-left-proofᵀ)


store-correspondence-drop-leftᵀ :
  StoreCorrespondenceDropLeftᵀ
store-correspondence-drop-leftᵀ liftρ corr =
  store-correspondence-drop-left-proofᵀ liftρ corr
