module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupDef
  where

-- File Charter:
--   * Defines identity-path representative-inst catch-up after exposing the
--     ordinary universal representative as paired or source-only.
--   * Retains both original self-permutation witnesses and the complete
--     quotiented term relation; it does not dequotient physical endpoints.
--   * Contains no implementation or recursive simulation dependency.

import Coercions as C
open import Data.List using ([])
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; `∀)
open import proof.ForallPermutationProperties using
  (AllImprecisionView)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term} {B E C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {C≈C : `∀ E ≈∀ `∀ E}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ `∀ E ⊑ C′ ⊣ Δᴿ}
    {C′≈C′ : C′ ≈∀ C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  AllImprecisionView C⊑C′ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ d ⟩) ⟨ C.inst B s ⟩) →
  Value (V ⟨ d ⟩) →
  No• (V ⟨ d ⟩) →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ `∀ E ⊑ᵖ C′
      ∶ quotientᵖ C≈C C⊑C′ C′≈C′ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (`∀ E) C′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
