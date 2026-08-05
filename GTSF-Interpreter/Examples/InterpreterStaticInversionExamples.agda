module Examples.InterpreterStaticInversionExamples where

-- File Charter:
--   * Regression-checks static root inversion through two allocation
--     prefixes.
--   * Keeps the example symbolic so it covers application, polymorphic, and
--     coercion-application roots uniformly.
--   * Uses no interpreter execution or reduction.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Typing.InterpreterStaticInversion using
  ( StaticInversionView
  ; static-inversion-view
  )
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; allocation-prefixᵀ
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)

two-prefixes-produce-static-view :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ₁ ρ₂ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    (prefix₀₁ : StoreImpPrefix ρ₀ ρ₁)
    (prefix₁₂ : StoreImpPrefix ρ₁ ρ₂)
    (inner :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  Δᴸ ∣ leftStoreⁱ ρ₁ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ₁ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Δᴸ ∣ leftStoreⁱ ρ₂ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ₂ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  StaticInversionView ρ₂ γ M M′ A B p
two-prefixes-produce-static-view
    prefix₀₁ prefix₁₂ inner
    source₁ target₁ source₂ target₂ =
  static-inversion-view
    (allocation-prefixᵀ prefix₁₂
      (allocation-prefixᵀ prefix₀₁ inner source₁ target₁)
      source₂ target₂)
