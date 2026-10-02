module proof.DGG.SimSourceAllClosingProof where

-- File Charter:
--   * Exposes the fixed source-only universal-closing adapter name.
--   * The intended adapter consumes value catchup and the post-catchup redex
--     core; the live M6 catchup result does not carry parked evolution, so
--     the catchup-to-Sim prefix is a named residual parameter.
--   * Contains no proof term beyond forwarding the residual parameter.

open import proof.DGG.Catchup.ValueCatchupRightDef
  using (ValueCatchupRight²)
open import proof.DGG.SourceAllValueRedexClosingDef
  using (SourceAllValueRedexClosingᵀ)
open import proof.DGG.SimSourceAllClosingDef
  using (SimSourceAllClosingᵀ)


SimSourceAllClosingAdapterResidualᵀ : Set
SimSourceAllClosingAdapterResidualᵀ =
  ValueCatchupRight²
  → SourceAllValueRedexClosingᵀ
  → SimSourceAllClosingᵀ


module _
    (sim-source-all-closing-adapter-residual :
      SimSourceAllClosingAdapterResidualᵀ)
  where

  sim-source-all-closing-from-value-redex :
    ValueCatchupRight²
    → SourceAllValueRedexClosingᵀ
    → SimSourceAllClosingᵀ
  sim-source-all-closing-from-value-redex =
    sim-source-all-closing-adapter-residual
