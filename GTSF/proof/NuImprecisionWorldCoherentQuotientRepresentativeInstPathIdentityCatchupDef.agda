module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupDef
  where

-- File Charter:
--   * Defines representative-inst catch-up when both normalized permutation
--     paths are identities.
--   * Retains the original possibly non-canonical permutation witnesses in
--     the quotient relation index.
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
open import Types using (Ty)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term} {B C C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {C≈C : C ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈C′ : C′ ≈∀ C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
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
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ C ⊑ᵖ C′
      ∶ quotientᵖ C≈C C⊑C′ C′≈C′ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ C C′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
