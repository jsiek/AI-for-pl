module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropLemma
  where

-- File Charter:
--   * Exposes the canonical matched-body source-only
--     commute/lift/transport/drop theorem.
--   * Keeps callers independent of the worker proof.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropDef
  using (RightSourceOnlyAllBodyTransportDropᵀ)
open import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropProof
  using (right-source-only-all-body-transport-drop-proofᵀ)


right-source-only-all-body-transport-dropᵀ :
  RightSourceOnlyAllBodyTransportDropᵀ
right-source-only-all-body-transport-dropᵀ
    {χs = χs} transport q =
  right-source-only-all-body-transport-drop-proofᵀ
    {χs = χs} transport q
