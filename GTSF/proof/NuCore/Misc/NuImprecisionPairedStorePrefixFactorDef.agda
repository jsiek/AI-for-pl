module proof.NuCore.Misc.NuImprecisionPairedStorePrefixFactorDef where

-- File Charter:
--   * Defines factorization of a matched store lift through an ambient
--     relational-store prefix.
--   * Exposes the lifted relational suffix and its corresponding lifted
--     prefix for use by paired-binder closing proofs.
--   * Contains no implementation, term imprecision, conversion, postulate,
--     hole, permissive option, handler import, or simulation import.

open import Data.Product using (_×_; ∃-syntax)
open import Data.Nat using (suc)
open import NuTermImprecision using (LiftStoreⁱ; StoreImp)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import ImprecisionWf using (ImpCtx)
open import Types using (TyCtx)


PairedStorePrefixFactorᵀ : Set
PairedStorePrefixFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ⁺∀ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftStoreⁱ Ψ ρ⁺ ρ⁺∀ →
  ∃[ ρ₀∀ ]
    LiftStoreⁱ Ψ ρ₀ ρ₀∀ × StoreImpPrefix ρ₀∀ ρ⁺∀
