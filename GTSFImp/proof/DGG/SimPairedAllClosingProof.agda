module proof.DGG.SimPairedAllClosingProof where

-- File Charter:
--   * Exposes the fixed paired universal-closing adapter name.
--   * The intended adapter consumes value catchup and the post-catchup redex
--     core; the live M6 catchup result does not carry parked evolution, so
--     the catchup-to-Sim prefix is a named residual parameter.
--   * Contains no proof term beyond forwarding the residual parameter.

open import proof.DGG.Catchup.ValueCatchupRightDef
  using (ValueCatchupRight²)
open import proof.DGG.PairedAllValueRedexClosingDef
  using (PairedAllValueRedexClosingᵀ)
open import proof.DGG.SimPairedAllClosingDef
  using (SimPairedAllClosingᵀ)


SimPairedAllClosingAdapterResidualᵀ : Set
SimPairedAllClosingAdapterResidualᵀ =
  ValueCatchupRight²
  → PairedAllValueRedexClosingᵀ
  → SimPairedAllClosingᵀ


module _
    (sim-paired-all-closing-adapter-residual :
      SimPairedAllClosingAdapterResidualᵀ)
  where

  sim-paired-all-closing-from-value-redex :
    ValueCatchupRight²
    → PairedAllValueRedexClosingᵀ
    → SimPairedAllClosingᵀ
  sim-paired-all-closing-from-value-redex =
    sim-paired-all-closing-adapter-residual
