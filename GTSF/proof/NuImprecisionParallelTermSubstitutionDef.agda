module proof.NuImprecisionParallelTermSubstitutionDef where

-- File Charter:
--   * States same-world parallel term substitution for no-bullet
--     quotiented Nu-term imprecision.
--   * States the structurally recursive framed theorem and its public
--     frame-identity specialization.
--   * Uses a genuine environment family so arbitrary precision indices stored
--     in type-binder context lifts remain available without proof irrelevance.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Substˣ; Term; substˣᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionEnvironmentFamily
  ; QuotientedSubstitutionFrame
  )


QuotientedParallelTermSubstitutionFramedᵀ : Set₁
QuotientedParallelTermSubstitutionFramedᵀ =
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ} →
  (environment : QuotientedSubstitutionEnvironmentFamily
    ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {N N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  QuotientedSubstitutionFrame ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
    ρ⁺ γ δ τ τ′ →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• N → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
    ⊢ᴺ substˣᵐ τ N ⊑ substˣᵐ τ′ N′ ⦂ A ⊑ B ∶ p


QuotientedParallelTermSubstitutionᵀ : Set₁
QuotientedParallelTermSubstitutionᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {N N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  QuotientedSubstitutionEnvironmentFamily ρ γ δ τ τ′ →
  No• N → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
    ⊢ᴺ substˣᵐ τ N ⊑ substˣᵐ τ′ N′ ⦂ A ⊑ B ∶ p
