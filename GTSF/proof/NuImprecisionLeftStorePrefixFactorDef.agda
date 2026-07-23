module proof.NuImprecisionLeftStorePrefixFactorDef where

-- File Charter:
--   * States left-store lifting factorization through an ambient
--     relational-store prefix.
--   * Produces the lifted smaller store and preserves its prefix relation to
--     the already-lifted ambient store.
--   * Completes the left/paired/right factorization family needed beneath
--     type binders.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.Nat using (suc)
open import Data.Product using (_×_; ∃-syntax)

open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (LiftLeftStoreⁱ; StoreImp)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (TyCtx)


LeftStorePrefixFactorᵀ : Set
LeftStorePrefixFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ⁺ᴸ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftLeftStoreⁱ Ψ ρ⁺ ρ⁺ᴸ →
  ∃[ ρ₀ᴸ ]
    LiftLeftStoreⁱ Ψ ρ₀ ρ₀ᴸ ×
    StoreImpPrefix ρ₀ᴸ ρ⁺ᴸ
