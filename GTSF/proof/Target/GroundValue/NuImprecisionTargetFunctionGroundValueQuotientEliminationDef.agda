module proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationDef where

-- File Charter:
--   * Defines quotient elimination when the target type is `★ ⇒ ★`.
--   * Returns an explicit ordinary imprecision index and term relation.
--   * Contains no implementation, result carrier, or simulation dependency.

open import Data.List using ([])
open import Data.Product using (∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term; Value)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; ★; _⇒_)


TargetFunctionGroundValueQuotientEliminationᵀ : Set₁
TargetFunctionGroundValueQuotientEliminationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {D : Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ (★ ⇒ ★) ⊣ Δᴿ} →
  Value V →
  Value V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⊑ V′ ⦂ D ⊑ᵖ (★ ⇒ ★) ∶ qD →
  ∃[ q ]
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ V′ ⦂ D ⊑ (★ ⇒ ★) ∶ q
