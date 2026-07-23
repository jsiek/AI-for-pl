module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathTargetStepCatchupDef
  where

-- File Charter:
--   * Defines representative-inst catch-up after the source path is exhausted
--     and one leading normalized target permutation step remains.
--   * Keeps the elementary target step and residual target path explicit.
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
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using (_↝∀_; _≈∀ⁿ_)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B C C′ E′ D′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {C≈C : C ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈D′ : C′ ≈∀ D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {step : C′ ↝∀ E′}
    {rest : E′ ≈∀ⁿ D′} →
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
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ C ⊑ᵖ D′
      ∶ quotientᵖ C≈C C⊑C′ C′≈D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ C D′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
