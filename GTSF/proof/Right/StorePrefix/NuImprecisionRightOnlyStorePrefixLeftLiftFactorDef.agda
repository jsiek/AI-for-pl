module
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixLeftLiftFactorDef
  where

-- File Charter:
--   * Defines factorization of a target-only store prefix across a
--     source-only store lift.
--   * Produces the target-extended base store, its target-only prefix, and
--     the corresponding extended source-only lift.
--   * Contains no implementation, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using (LiftLeftStoreⁱ; StoreImp)
open import Types using (TyCtx)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)


RightOnlyStorePrefixLeftLiftFactorᵀ : Set
RightOnlyStorePrefixLeftLiftFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ ρ⁺ᴸ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρᴸ →
  RightOnlyStoreImpPrefix ρᴸ ρ⁺ᴸ →
  Σ[ ρ⁺ ∈ StoreImp Φ Δᴸ Δᴿ ]
    RightOnlyStoreImpPrefix ρ ρ⁺ ×
    LiftLeftStoreⁱ Ψ ρ⁺ ρ⁺ᴸ
