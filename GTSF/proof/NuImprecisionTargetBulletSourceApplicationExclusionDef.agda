module proof.NuImprecisionTargetBulletSourceApplicationExclusionDef where

-- File Charter:
--   * Defines the structural exclusion of a QTI relation from a source
--     application to a target runtime bullet.
--   * Reuses the bullet constructor's underlying target-value obligation.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Data.Empty using (⊥)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (CtxImp; StoreImp)
open import NuTerms using
  (Term; _•; _·_)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)


QuotientedTargetBulletExcludesSourceApplicationᵀ : Set₁
QuotientedTargetBulletExcludesSourceApplicationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {L M N : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ L · M ⊑ N • ⦂ A ⊑ B ∶ p →
  ⊥
