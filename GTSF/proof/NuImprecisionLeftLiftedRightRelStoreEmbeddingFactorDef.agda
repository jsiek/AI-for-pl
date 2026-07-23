module
  proof.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorDef
  where

-- File Charter:
--   * Defines inverse factorization of a target-only relational-store
--     embedding beneath a source-only store lift.
--   * Recovers the target-evolved base store, its embedding from the
--     original base, and the corresponding final source-only lift.
--   * Contains no implementation, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.Product using (_×_; Σ-syntax)
open import Data.Nat using (suc)
open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (LiftLeftStoreⁱ; StoreImp)
open import Types using (Renameᵗ; TyCtx)
open import proof.MaximalLowerBoundsWf using (νᵢᶜ)
open import proof.NuImprecisionRelStoreEmbeddingDef using
  (RelStoreEmbeddingⁱ)


LeftLiftedRightRelStoreEmbeddingFactorᵀ : Set₁
LeftLiftedRightRelStoreEmbeddingFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴿ : TyCtx}
    {σ : Renameᵗ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
    {ρ′ᴸ : StoreImp (νᵢᶜ Ψ) (suc Δᴸ) Θᴿ} →
  LiftLeftStoreⁱ (νᵢᶜ Φ) ρ ρᴸ →
  RelStoreEmbeddingⁱ (λ X → X) σ ρᴸ ρ′ᴸ →
  Σ[ ρ′ ∈ StoreImp Ψ Δᴸ Θᴿ ]
    LiftLeftStoreⁱ (νᵢᶜ Ψ) ρ′ ρ′ᴸ ×
    RelStoreEmbeddingⁱ (λ X → X) σ ρ ρ′
