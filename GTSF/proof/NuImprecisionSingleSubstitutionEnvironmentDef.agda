module proof.NuImprecisionSingleSubstitutionEnvironmentDef where

-- File Charter:
--   * States construction of the complete binder-frame environment family for
--     one related pair of substitution arguments.
--   * Makes arbitrary precision indices stored in paired and source-only
--     context lifts part of the explicit hard proof obligation.
--   * Isolates the remaining environment-lifting theorem needed to derive
--     single substitution from parallel substitution.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using (_∷_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Term; singleEnv)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionSubstitutionFrame using
  (QuotientedSubstitutionEnvironmentFamily)


QuotientedSingleSubstitutionEnvironmentᵀ : Set₁
QuotientedSingleSubstitutionEnvironmentᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {A A′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  No• V → No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  QuotientedSubstitutionEnvironmentFamily
    ρ (ctx-imp A A′ pA ∷ γ) γ
    (singleEnv V) (singleEnv V′)
