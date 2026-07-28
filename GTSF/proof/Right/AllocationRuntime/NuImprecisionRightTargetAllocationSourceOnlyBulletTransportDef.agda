module proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceOnlyBulletTransportDef where

-- File Charter:
--   * Defines the source-only runtime-bullet base case for transport across a
--     target allocation.
--   * Keeps both source typings because runtime bullets cannot use ordinary
--     no-bullet store weakening.
--   * Contains no implementation, postulate, hole, permissive option,
--     catch-all clause, or termination bypass.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; _•; ⇑ᵗᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx; WfTy; wf★; ★; `∀; ⇑ᵗ)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)


RightTargetAllocationSourceOnlyBulletTransportᵀ : Set₁
RightTargetAllocationSourceOnlyBulletTransportᵀ =
  ∀ {Φ₀ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ₀ Δᴸ Δᴿ}
    {ρᴸ ρ⁺ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀) (suc Δᴸ) Δᴿ}
    {ρᴿ⁺ : StoreImp
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀))
      (suc Δᴸ) (suc Δᴿ)}
    {L M′ : Term} {A B′ C : Ty}
    {h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {{safe : NonVar C}} {occ} →
  StoreImpPrefix
    (store-left zero (⇑ᵗ A) h⇑A ∷ ρᴸ) ρ⁺ →
  LiftRightStoreⁱ
    (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀)) ρ⁺ ρᴿ⁺ →
  AssumptionMembershipUnique
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀) →
  No• M′ →
  suc Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
    ⊢ (⇑ᵗᵐ L) • ⦂ C →
  Φ₀ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ M′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p →
  Value L →
  No• L →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀) ρ₀ ρᴸ →
  suc Δᴸ
    ∣ leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρᴸ)
    ∣ [] ⊢ (⇑ᵗᵐ L) • ⦂ C →
  ⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ₀)
    ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ M′
    ⦂ C ⊑ ⇑ᵗ B′ ∶ ⊑-target-lift-rightᵢ p
