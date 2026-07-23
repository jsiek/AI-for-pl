module proof.Store.Prefix.NuImprecisionStorePrefixLiftDef where

-- File Charter:
--   * States forward transport of paired and one-sided store lifts across a
--     relational-store prefix.
--   * Exposes the lifted extended store together with the corresponding
--     lifted prefix needed by substitution below type binders.
--   * Contains no implementation, term relation, postulate, hole, or
--     permissive option.

open import Data.Nat using (suc)
open import Data.Product using (_×_; ∃-syntax)

open import Data.List using (_∷_)
open import Data.Nat using (zero)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᴿᵢ; ⇑ᵢ)
open import NuTermImprecision using
  (LiftLeftStoreⁱ; LiftRightStoreⁱ; LiftStoreⁱ; StoreImp)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (TyCtx)


PairedStorePrefixLiftᵀ : Set
PairedStorePrefixLiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₀↑ →
  ∃[ ρ⁺↑ ]
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ⁺ ρ⁺↑ ×
    StoreImpPrefix ρ₀↑ ρ⁺↑


LeftStorePrefixLiftᵀ : Set
LeftStorePrefixLiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ₀↑ →
  ∃[ ρ⁺↑ ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ⁺ ρ⁺↑ ×
    StoreImpPrefix ρ₀↑ ρ⁺↑


RightStorePrefixLiftᵀ : Set
RightStorePrefixLiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ₀↑ →
  ∃[ ρ⁺↑ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρ⁺↑ ×
    StoreImpPrefix ρ₀↑ ρ⁺↑
