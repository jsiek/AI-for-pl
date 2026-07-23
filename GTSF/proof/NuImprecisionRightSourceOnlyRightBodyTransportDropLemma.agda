module
  proof.NuImprecisionRightSourceOnlyRightBodyTransportDropLemma
  where

-- File Charter:
--   * Exposes the canonical right-body source-only
--     commute/lift/transport/drop theorem.
--   * Keeps callers independent of the worker proof.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import
  proof.NuImprecisionRightSourceOnlyRightBodyTransportDropDef
  using (RightSourceOnlyRightBodyTransportDropᵀ)
open import
  proof.NuImprecisionRightSourceOnlyRightBodyTransportDropProof
  using (right-source-only-right-body-transport-drop-proofᵀ)


right-source-only-right-body-transport-dropᵀ :
  RightSourceOnlyRightBodyTransportDropᵀ
right-source-only-right-body-transport-dropᵀ
    {χs = χs} transport q =
  right-source-only-right-body-transport-drop-proofᵀ
    {χs = χs} transport q
