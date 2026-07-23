module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDropLeftStoreDef
  where

-- File Charter:
--   * Defines inverse transport of world coherence through a source-only
--     relational-store lift.
--   * Specializes the context to the canonical source-only head required by
--     the DGG source-universal closing factor.
--   * Contains no implementation, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.Nat using (suc)
open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (LiftLeftStoreⁱ; StoreImp)
open import Types using (TyCtx)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (νᵢᶜ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


WorldCoherenceDropLeftStoreᵀ : Set₁
WorldCoherenceDropLeftStoreᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ (νᵢᶜ Φ) ρ ρᴸ →
  WorldCoherent ρᴸ →
  WorldCoherent ρ
