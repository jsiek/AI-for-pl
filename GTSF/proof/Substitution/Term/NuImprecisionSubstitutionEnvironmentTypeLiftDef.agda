module proof.Substitution.Term.NuImprecisionSubstitutionEnvironmentTypeLiftDef where

-- File Charter:
--   * States paired and source-only type lifting of a related no-bullet
--     substitution environment.
--   * Targets the exact, potentially non-canonical precision indices stored in
--     `LiftCtxⁱ` and `LiftLeftCtxⁱ` rather than assuming proof irrelevance.
--   * Isolates the two hard binder leaves needed by the complete single-
--     substitution environment family.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  )
open import NuTerms using (No•; Substˣ; ↑ᵗᵐ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (TyCtx; _∋_⦂_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)


QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ : Set₁
QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ δ↑ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {τ τ′ : Substˣ} →
  AssumptionMembershipUnique Φ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ↑ →
  LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
  LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  (∀ x → No• (τ x)) →
  (∀ x → No• (τ′ x)) →
  (∀ {x A B p} →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ ↑ᵗᵐ τ x ⊑ ↑ᵗᵐ τ′ x ⦂ A ⊑ B ∶ p) ×
  (∀ x → No• (↑ᵗᵐ τ x)) ×
  (∀ x → No• (↑ᵗᵐ τ′ x))


QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ : Set₁
QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ δ↑ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {τ τ′ : Substˣ} →
  AssumptionMembershipUnique Φ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  (∀ x → No• (τ x)) →
  (∀ x → No• (τ′ x)) →
  (∀ {x A B p} →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ ↑ᵗᵐ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) ×
  (∀ x → No• (↑ᵗᵐ τ x)) ×
  (∀ x → No• (τ′ x))
