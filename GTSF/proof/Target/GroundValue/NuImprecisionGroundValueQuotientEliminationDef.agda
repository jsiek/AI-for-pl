module proof.Target.GroundValue.NuImprecisionGroundValueQuotientEliminationDef where

-- File Charter:
--   * Defines quotient elimination restricted to ground-related values.
--   * Returns an explicit ordinary imprecision index and term relation.
--   * Does not assert the false unrestricted quotient-to-ordinary principle.
--   * Contains no implementation or source-runtime dependency.

open import Data.List using ([])
open import Data.Product using (∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; Value)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ground; Ty)


GroundValueQuotientEliminationᵀ : Set₁
GroundValueQuotientEliminationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {G D′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ G ⊑ᵖ D′ ⊣ Δᴿ} →
  Ground G →
  Value V →
  Value V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⊑ V′ ⦂ G ⊑ᵖ D′ ∶ qD →
  ∃[ q ]
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ V′ ⦂ G ⊑ D′ ∶ q
