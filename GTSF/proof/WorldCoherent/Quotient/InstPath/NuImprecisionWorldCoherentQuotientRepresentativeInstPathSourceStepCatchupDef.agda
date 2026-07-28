module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepCatchupDef
  where

-- File Charter:
--   * Defines representative-inst catch-up for one leading normalized source
--     permutation step followed by arbitrary residual paths.
--   * Keeps the elementary step and both residual paths explicit for a future
--     reduction-and-continuation proof.
--   * Contains no implementation or recursive simulation dependency.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Data.List using ([])
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Core.Permutation.ForallPermutationPath
  using
  (_↝∀_; _≈∀ⁿ_; normalize-forall-permutation; path-step)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B D E D′ C C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {sU sU′ : ImprecisionShape}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {D≈C : D ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈D′ : C′ ≈∀ D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {step : D ↝∀ E}
    {rest : E ≈∀ⁿ C}
    {targetPath : C′ ≈∀ⁿ D′} →
  normalize-forall-permutation D≈C ≡ path-step step rest →
  normalize-forall-permutation C′≈D′ ≡ targetPath →
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
  widening ⊢ᶜ C.inst B s ⦂ sU →
  widening ⊢ᶜ u′ ⦂ sU′ →
  sU ；⌊ pA ⌋≋ᵖ
    quotientᵖ D≈C C⊑C′ C′≈D′ ； sU′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
