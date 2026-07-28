module
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionDef
  where

-- File Charter:
--   * Defines the structural exclusion of a QTI relation from a source value
--     to a target runtime bullet.
--   * Keeps the source-value evidence explicit so source universal and inert
--     cast frames can be peeled before the target-bullet root is exposed.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Data.Empty using (⊥)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using
  (Term; Value; _•)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)


QuotientedTargetBulletExcludesSourceValueᵀ : Set₁
QuotientedTargetBulletExcludesSourceValueᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {V L′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ L′ • ⦂ A ⊑ B ∶ p →
  ⊥
