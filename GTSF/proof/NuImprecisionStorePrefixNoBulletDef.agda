module proof.NuImprecisionStorePrefixNoBulletDef where

-- File Charter:
--   * States no-bullet quotiented term imprecision weakening through a
--     relational-store prefix.
--   * Keeps the terms, type contexts, term context, and precision index fixed.
--   * Exposes the store-prefix bridge needed by term substitution.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using (No•; Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx)


QuotientedStorePrefixNoBulletᵀ : Set₁
QuotientedStorePrefixNoBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M → No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p


QuotientedStorePrefixNoBulletᵖᵀ : Set₁
QuotientedStorePrefixNoBulletᵖᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {D D′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M → No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q
