module
  proof.Left.LiftedStore.NuImprecisionLeftLiftedStorePrefixFactorDef
  where

-- File Charter:
--   * Defines inverse factorization of a prefix beneath a source-only store
--     lift.
--   * Recovers the smaller base store, its prefix to the ambient base store,
--     and the corresponding source-only lift.
--   * Contains no implementation, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.Nat using (suc)
open import Data.Product using (_×_; ∃-syntax)
open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (LiftLeftStoreⁱ; StoreImp)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (TyCtx)


LeftLiftedStorePrefixFactorᵀ : Set
LeftLiftedStorePrefixFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀ᴸ ρ⁺ᴸ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ⁺ ρ⁺ᴸ →
  StoreImpPrefix ρ₀ᴸ ρ⁺ᴸ →
  ∃[ ρ₀ ]
    StoreImpPrefix ρ₀ ρ⁺ ×
    LiftLeftStoreⁱ Ψ ρ₀ ρ₀ᴸ
