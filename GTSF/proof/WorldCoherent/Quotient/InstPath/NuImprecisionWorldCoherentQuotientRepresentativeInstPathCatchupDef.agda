module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  where

-- File Charter:
--   * Defines oriented contextual adjacent swaps and their finite paths.
--   * Defines representative-inst catch-up with normalized permutation paths.
--   * Retains the original quotient proofs in the indexed term relation.
--   * Contains no dequotienting, simulation implementation, or dispatcher.

import Coercions as C
open import Data.List using ([])
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ; swap01ᵗ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; renameᵗ; _⇒_; `∀)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


infix 4 _↝∀_
data _↝∀_ : Ty → Ty → Set where
  element-swap : ∀ {A} →
    `∀ (`∀ A) ↝∀ `∀ (`∀ (renameᵗ swap01ᵗ A))

  element-unswap : ∀ {A} →
    `∀ (`∀ (renameᵗ swap01ᵗ A)) ↝∀ `∀ (`∀ A)

  element-arrow-left : ∀ {A A′ B} →
    A ↝∀ A′ →
    A ⇒ B ↝∀ A′ ⇒ B

  element-arrow-right : ∀ {A B B′} →
    B ↝∀ B′ →
    A ⇒ B ↝∀ A ⇒ B′

  element-all : ∀ {A B} →
    A ↝∀ B →
    `∀ A ↝∀ `∀ B

infix 4 _≈∀ⁿ_
data _≈∀ⁿ_ : Ty → Ty → Set where
  path-refl : ∀ {A} →
    A ≈∀ⁿ A

  path-step : ∀ {A B C} →
    A ↝∀ B →
    B ≈∀ⁿ C →
    A ≈∀ⁿ C


WorldCoherentQuotientRepresentativeInstPathCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B D D′ C C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {D≈C : D ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈D′ : C′ ≈∀ D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  D ≈∀ⁿ C →
  C′ ≈∀ⁿ D′ →
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
