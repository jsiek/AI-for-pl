module proof.NuImprecisionTargetValueSourceApplicationExclusionDef where

-- File Charter:
--   * Defines the structural exclusion of a QTI relation from a source
--     application to a target value.
--   * Provides a reusable boundary for both source application beta roots.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Data.Empty using (⊥)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (CtxImp; StoreImp)
open import NuTerms using
  (Term; Value; _·_)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)


QuotientedTargetValueExcludesSourceApplicationᵀ : Set₁
QuotientedTargetValueExcludesSourceApplicationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {L M V : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ L · M ⊑ V ⦂ A ⊑ B ∶ p →
  Value V →
  ⊥
