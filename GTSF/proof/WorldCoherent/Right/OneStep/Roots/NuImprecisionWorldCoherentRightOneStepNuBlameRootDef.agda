module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootDef
  where

-- File Charter:
--   * Defines the target `blame-ν` root when source and target both retain an
--     outer `ν`.
--   * Requires only the related bodies; the source body is caught up to
--     blame and the surrounding source `ν` then propagates blame.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; blame
  ; ν
  )
open import Coercions using (Coercion)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentRightOneStepNuBlameRootᵀ : Set₁
WorldCoherentRightOneStepNuBlameRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N : Term} {A C C′ B B′ : Ty} {s : Coercion}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  RuntimeOK (ν A N s) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ blame ⦂ C ⊑ C′ ∶ q →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = blame} {χ = keep} {ρ = ρ} p
