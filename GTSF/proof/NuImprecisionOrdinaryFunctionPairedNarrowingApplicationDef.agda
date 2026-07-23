module
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  where

-- File Charter:
--   * Defines quotient application introduction for an ordinary function and
--     an ordinarily related argument under paired cast-mode narrowings.
--   * Keeps the quotient at the application boundary instead of exposing an
--     unrestricted paired-narrowing quotient.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Coercions using (Coercion)
open import Data.List using ([])

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; _⇒_)


OrdinaryFunctionPairedNarrowingApplicationᵀ : Set₁
OrdinaryFunctionPairedNarrowingApplicationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ : Term} {d d′ : Coercion}
    {A A′ C C′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {qB : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ}
    {μ μ′} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ A ⊒ C →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ A′ ⊒ C′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
      ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ L · (M ⟨ d ⟩) ⊑ L′ · (M′ ⟨ d′ ⟩)
      ⦂ B ⊑ᵖ B′ ∶ qB
