module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionLambdaDef where

-- File Charter:
--   * States the ordinary-lambda constructor case of prefix-aware parallel
--     substitution.
--   * Carries the current binder frame and the complete environment family so
--     the recursive body uses the exact extended precision context.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using (_∷_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_; _↦_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Substˣ; Term; ƛ_; extˢˣ; substˣᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; WfTy; _⇒_)
open import proof.Substitution.Term.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionEnvironmentFamily
  ; QuotientedSubstitutionFrame
  )


QuotientedParallelTermSubstitutionLambdaᵀ : Set₁
QuotientedParallelTermSubstitutionLambdaᵀ =
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ} →
  (environment : QuotientedSubstitutionEnvironmentFamily
    ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {N N′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  QuotientedSubstitutionFrame ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
    ρ⁺ γ δ τ τ′ →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• N → No• N′ →
  WfTy Δᴸ A → WfTy Δᴿ A′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ ctx-imp A A′ pA ∷ γ
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
    ⊢ᴺ ƛ substˣᵐ (extˢˣ τ) N
      ⊑ ƛ substˣᵐ (extˢˣ τ′) N′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB
