module proof.DGG.SimPairedFunClosingProof where

-- File Charter:
--   * Exposes the fixed paired function-closing adapter name.
--   * The intended adapter consumes value catchup and the D8a
--     single-substitution corollary; the beta/cast-function row assembly is
--     kept as a named residual parameter on this branch.
--   * Contains no proof term beyond forwarding the residual parameter.

open import proof.DGG.Catchup.ValueCatchupRightDef
  using (ValueCatchupRight²)
open import proof.DGG.SimPairedFunClosingDef
  using (SimPairedFunClosingᵀ)
open import proof.DGG.TermSubstClosingDef
  using (⊢²-single-substᵀ)


SimPairedFunClosingAdapterResidualᵀ : Set
SimPairedFunClosingAdapterResidualᵀ =
  ValueCatchupRight²
  → ⊢²-single-substᵀ
  → SimPairedFunClosingᵀ


module _
    (sim-paired-fun-closing-adapter-residual :
      SimPairedFunClosingAdapterResidualᵀ)
  where

  sim-paired-fun-closing-from-single-subst :
    ValueCatchupRight²
    → ⊢²-single-substᵀ
    → SimPairedFunClosingᵀ
  sim-paired-fun-closing-from-single-subst =
    sim-paired-fun-closing-adapter-residual
