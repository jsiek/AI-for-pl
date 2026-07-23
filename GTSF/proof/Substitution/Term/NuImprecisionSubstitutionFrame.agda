module proof.Substitution.Term.NuImprecisionSubstitutionFrame where

-- File Charter:
--   * Defines the genuine binder-frame structure for quotiented parallel term
--     substitution.
--   * Tracks ordinary lambda extension and paired or source-only type lifting
--     of the relation world, contexts, and substitution images.
--   * Defines the environment-family obligation at every reachable frame.
--   * Contains no theorem implementation, postulate, hole, or permissive
--     option.

open import Data.List using (_∷_)
open import Data.Nat using (zero)
open import Data.Product using (_×_)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; ctx-imp
  )
open import NuTerms using (No•; Substˣ; extˢˣ; ↑ᵗᵐ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (TyCtx; _∋_⦂_)


data QuotientedSubstitutionFrame
    {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    (ρ₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ)
    (γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ)
    (τ₀ τ₀′ : Substˣ) :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
    StoreImp Φ Δᴸ Δᴿ →
    CtxImp Φ Δᴸ Δᴿ →
    CtxImp Φ Δᴸ Δᴿ →
    Substˣ → Substˣ → Set₁ where
  substitution-frame-id :
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ₀ γ₀ δ₀ τ₀ τ₀′

  substitution-frame-ƛ :
    ∀ {Φ Δᴸ Δᴿ ρ γ δ τ τ′ A A′ pA} →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ
      (ctx-imp A A′ pA ∷ γ)
      (ctx-imp A A′ pA ∷ δ)
      (extˢˣ τ) (extˢˣ τ′)

  substitution-frame-Λ :
    ∀ {Φ Δᴸ Δᴿ ρ ρ↑ γ γ↑ δ δ↑ τ τ′} →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ↑ γ↑ δ↑ (↑ᵗᵐ τ) (↑ᵗᵐ τ′)

  substitution-frame-Λ-left :
    ∀ {Φ Δᴸ Δᴿ ρ ρ↑ γ γ↑ δ δ↑ τ τ′} →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ →
    QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ↑ γ↑ δ↑ (↑ᵗᵐ τ) τ′


QuotientedSubstitutionEnvironmentFamily :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
  StoreImp Φ Δᴸ Δᴿ →
  CtxImp Φ Δᴸ Δᴿ →
  CtxImp Φ Δᴸ Δᴿ →
  Substˣ → Substˣ → Set₁
QuotientedSubstitutionEnvironmentFamily ρ₀ γ₀ δ₀ τ₀ τ₀′ =
  ∀ {Φ Δᴸ Δᴿ ρ γ δ τ τ′} →
  QuotientedSubstitutionFrame ρ₀ γ₀ δ₀ τ₀ τ₀′
    {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) ×
  (∀ x → No• (τ x)) ×
  (∀ x → No• (τ′ x))
