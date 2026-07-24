module proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportDef where

-- File Charter:
--   * Defines flat source-bullet transport across a target allocation.
--   * Exposes the administrative source-store prefix and the right lift needed
--     to reconstruct the allocated target store.
--   * Returns the exact target-lifted QTI derivation without an intermediate
--     result carrier.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; wf★
  ; ★
  ; ⇑ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)


RightTargetAllocationSourceBulletTransportᵀ : Set₁
RightTargetAllocationSourceBulletTransportᵀ =
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {L M′ : Term} {A B : Ty}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺ →
  AssumptionMembershipUnique Φ →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
    ⊢ (⇑ᵗᵐ L) • ⦂ A →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ M′ ⦂ A ⊑ B ∶ q →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
    ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ M′
    ⦂ A ⊑ ⇑ᵗ B ∶ ⊑-target-lift-rightᵢ q
