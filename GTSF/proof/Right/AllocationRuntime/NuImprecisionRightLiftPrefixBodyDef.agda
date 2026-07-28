module
  proof.Right.AllocationRuntime.NuImprecisionRightLiftPrefixBodyDef
  where

-- File Charter:
--   * Defines target-only right-lift transport under an arbitrary relational-
--     store prefix.
--   * Isolates the exact support contract used by target allocation lineage
--     and transport proofs from the broad simulation implementation.
--   * Contains no implementation, dispatcher, or permissive option.

open import Data.List using ([])
open import Data.Nat using (suc)
open import ImprecisionWf using
  (ImpCtx; ⇑ᴿᵢ; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftRightStoreⁱ
  ; StoreImp
  )
open import NuTerms using (No•; Term; ⇑ᵗᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; ⇑ᵗ)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-target-lift-rightᵢ)


RightLiftPrefixBodyᵀ : Set₁
RightLiftPrefixBodyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B : Ty} {L L′ : Term}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ⁺ →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ L ⊑ ⇑ᵗᵐ L′ ⦂ A ⊑ ⇑ᵗ B
      ∶ ⊑-target-lift-rightᵢ p
