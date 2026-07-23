module
  proof.NuImprecisionRightSourceOnlyTransportDropLemma
  where

-- File Charter:
--   * Exposes the canonical source-only lift/transport/drop theorem.
--   * Keeps callers independent of the worker proof.
--   * Contains no simulation result, catch-up carrier, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import
  proof.NuImprecisionRightSourceOnlyTransportDropDef
  using (RightSourceOnlyTransportDropᵀ)
open import
  proof.NuImprecisionRightSourceOnlyTransportDropProof
  using (right-source-only-transport-drop-proofᵀ)


right-source-only-transport-dropᵀ :
  RightSourceOnlyTransportDropᵀ
right-source-only-transport-dropᵀ
    {χs = χs} transport q =
  right-source-only-transport-drop-proofᵀ
    {χs = χs} transport q
