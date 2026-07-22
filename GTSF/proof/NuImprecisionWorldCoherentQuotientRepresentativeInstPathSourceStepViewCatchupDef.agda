module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupDef
  where

-- File Charter:
--   * Defines leading-source-step quotient-inst catch-up after typed `inst`
--     inversion has removed both impossible arrow-context path cases.
--   * Exposes only top swap, top unswap, and under-`forall` steps through
--     `SourceInstStepView`.
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
open import proof.NuImprecisionQuotientInstPathProperties using
  (SourceInstStepView)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using (_↝∀_; _≈∀ⁿ_)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathSourceStepViewCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B D E D′ C C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {D≈C : D ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈D′ : C′ ≈∀ D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {step : D ↝∀ E}
    {rest : E ≈∀ⁿ C}
    {targetPath : C′ ≈∀ⁿ D′} →
  SourceInstStepView step →
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
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ D ⊑ᵖ D′
      ∶ quotientᵖ D≈C C⊑C′ C′≈D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ D D′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
