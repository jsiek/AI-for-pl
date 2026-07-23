module proof.Substitution.Term.NuImprecisionLambdaSubstitutionEnvironmentDef where

-- File Charter:
--   * States extension of a related no-bullet parallel substitution
--     environment beneath an ordinary lambda binder.
--   * Uses the independent term-context shift boundary for successor images.
--   * Contains no relation traversal, postulate, hole, or permissive option.

open import Data.List using (_∷_)
open import Data.Product using (_×_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Substˣ; extˢˣ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; _∋_⦂_)
open import proof.Substitution.Term.NuImprecisionTermContextShiftDef using
  (QuotientedTermContextShiftᵀ)


QuotientedLambdaSubstitutionEnvironmentᵀ : Set₁
QuotientedLambdaSubstitutionEnvironmentᵀ =
  QuotientedTermContextShiftᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {A A′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (∀ {x C C′ q} →
    γ ∋ x ⦂ ctx-imp C C′ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ C ⊑ C′ ∶ q) →
  (∀ x → No• (τ x)) →
  (∀ x → No• (τ′ x)) →
  (∀ {x C C′ q} →
    ctx-imp A A′ pA ∷ γ ∋ x ⦂ ctx-imp C C′ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ δ
      ⊢ᴺ extˢˣ τ x ⊑ extˢˣ τ′ x ⦂ C ⊑ C′ ∶ q) ×
  (∀ x → No• (extˢˣ τ x)) ×
  (∀ x → No• (extˢˣ τ′ x))
