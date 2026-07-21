module proof.NuImprecisionLeftLiftPrefixBodyDef where

-- File Charter:
--   * Defines source-only left-lift transport under an arbitrary relational-
--     store prefix.
--   * Isolates the exact support contract used by source allocation lineage
--     and transport proofs from the broad simulation implementation.
--   * Contains no implementation, dispatcher, or permissive option.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _ˣ⊑★; ⇑ᴸᵢ)
open import NuTermImprecision using
  (LiftLeftStoreⁱ; StoreImp)
open import NuTerms using (No•; Term; ⇑ᵗᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; ⇑ᵗ)
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)


LeftLiftPrefixBodyᵀ : Set₁
LeftLiftPrefixBodyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B : Ty} {L L′ : Term}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ ρ⁺ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ⁺ →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ ⇑ᵗᵐ L ⊑ L′ ⦂ ⇑ᵗ A ⊑ B ∶ ⊑-source-liftνᵢ p
