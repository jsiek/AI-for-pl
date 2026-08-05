module Narrowing.InterpreterReachableCoercionNarrowingProperties where

-- File Charter:
--   * Exposes relational-store-prefix transport for reachable coercion plans.
--   * Preserves the distinction between paired conversions, one-sided
--     operational casts, and target-only static narrowings.
--   * Delegates the structural proof to a reduction-free proof module.

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing using (CoercionAction)
open import Narrowing.InterpreterReachableCoercionNarrowing
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (Ty; TyCtx)
import proof.InterpreterReachableCoercionNarrowingProof as Proof


reachable-component-prefix :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {left right : CoercionAction}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ReachableComponentCoercionNarrowing
    Φ Δᴸ Δᴿ ρ₀ left right p q →
  ReachableComponentCoercionNarrowing
    Φ Δᴸ Δᴿ ρ⁺ left right p q
reachable-component-prefix =
  Proof.reachable-component-prefix
