module proof.Right.StorePrefix.NuImprecisionRightStorePrefixFactorDef where

-- File Charter:
--   * States the right-store lifting factor used beneath an ambient store
--     prefix.
--   * Produces the lifted smaller store and preserves its prefix relation to
--     the already-lifted ambient store.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.Nat using (suc)
open import Data.Product using (_×_; ∃-syntax)

open import NuTermImprecision using
  (LiftRightStoreⁱ; StoreImp)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import ImprecisionWf using (ImpCtx)
open import Types using (TyCtx)


RightStorePrefixFactorᵀ : Set
RightStorePrefixFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ⁺ᴿ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftRightStoreⁱ Ψ ρ⁺ ρ⁺ᴿ →
  ∃[ ρ₀ᴿ ]
    LiftRightStoreⁱ Ψ ρ₀ ρ₀ᴿ ×
    StoreImpPrefix ρ₀ᴿ ρ⁺ᴿ
