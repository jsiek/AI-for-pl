module
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingDef
  where

-- File Charter:
--   * States the matched relation exposed after post-allocation `β-gen•`
--     on both sides.
--   * Produces only the paired narrowing quotient edge; operational reduction
--     steps remain the responsibility of simulation up to reduction.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or legacy allocation-simulation dependency.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; narrowing)
open import Coercions using (Coercion; gen; id-onlyᵈ)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms using (Term; ⇑ᵗᵐ; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (QuotientNarrowingEliminationCompatible)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx; `∀; ⇑ᵗ)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (CtxImp)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-matched
  )


MatchedPostAllocationBetaGenNarrowingRelationᵀ : Set₁
MatchedPostAllocationBetaGenNarrowingRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {Aν Aν′ A A′ B B′ : Ty} {V V′ : Term}
    {c c′ : Coercion} {p s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ′ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ gen A c ∶ A ⊒ `∀ B →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ gen A′ c′ ∶ A′ ⊒ `∀ B′ →
  narrowing ⊢ᶜ c ⦂ s →
  narrowing ⊢ᶜ c′ ⦂ s′ →
  (pν : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ Aν ⊑ Aν′ ⊣ suc Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-matched zero Aν zero Aν′ pν ∷ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ V ⊑ ⇑ᵗᵐ V′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ A′ ∶ p →
  (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ B ⊑ᵖ B′ ⊣ suc Δᴿ) →
  s ；⌊ p ⌋≋ᵖ q ； s′ →
  QuotientNarrowingEliminationCompatible
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    (suc Δᴸ) (suc Δᴿ) c c′ p q s s′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-matched zero Aν zero Aν′ pν ∷ ρ′ ∣ γ′
    ⊢ᴺᵖ (⇑ᵗᵐ V) ⟨ c ⟩ ⊑ (⇑ᵗᵐ V′) ⟨ c′ ⟩
    ⦂ B ⊑ᵖ B′ ∶ q
