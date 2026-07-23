module proof.NuImprecisionTermSubstitutionDef where

-- File Charter:
--   * States single term-variable substitution for quotiented Nu-term
--     imprecision.
--   * Relates substitution into no-bullet bodies in one relational world.
--   * Exposes the reusable semantic obligation needed by ordinary lambda beta.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using (_∷_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Term; _[_])
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)


QuotientedTermSubstitutionᵀ : Set₁
QuotientedTermSubstitutionᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  No• N → No• N′ → No• V → No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N [ V ] ⊑ N′ [ V′ ] ⦂ B ⊑ B′ ∶ pB
