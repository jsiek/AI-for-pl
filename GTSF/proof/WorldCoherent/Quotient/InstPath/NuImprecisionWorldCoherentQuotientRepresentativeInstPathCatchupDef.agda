module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  where

-- File Charter:
--   * Defines oriented contextual adjacent swaps and their finite paths.
--   * Defines representative-inst catch-up with normalized permutation paths.
--   * Retains the original quotient proofs in the indexed term relation.
--   * Contains no dequotienting, simulation implementation, or dispatcher.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Data.List using ([])
open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  ; swap01ᵗ
  )
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


elementary-forall-permutation-sym :
  ∀ {A B} →
  A ↝∀ B →
  B ↝∀ A
elementary-forall-permutation-sym element-swap = element-unswap
elementary-forall-permutation-sym element-unswap = element-swap
elementary-forall-permutation-sym
    (element-arrow-left step) =
  element-arrow-left (elementary-forall-permutation-sym step)
elementary-forall-permutation-sym
    (element-arrow-right step) =
  element-arrow-right (elementary-forall-permutation-sym step)
elementary-forall-permutation-sym (element-all step) =
  element-all (elementary-forall-permutation-sym step)

forall-permutation-path-trans :
  ∀ {A B C} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ C →
  A ≈∀ⁿ C
forall-permutation-path-trans path-refl B≈C = B≈C
forall-permutation-path-trans (path-step step A≈B) B≈C =
  path-step step (forall-permutation-path-trans A≈B B≈C)

forall-permutation-path-sym :
  ∀ {A B} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ A
forall-permutation-path-sym path-refl = path-refl
forall-permutation-path-sym (path-step step B≈C) =
  forall-permutation-path-trans
    (forall-permutation-path-sym B≈C)
    (path-step (elementary-forall-permutation-sym step) path-refl)

forall-permutation-path-arrow-left :
  ∀ {A A′ B} →
  A ≈∀ⁿ A′ →
  A ⇒ B ≈∀ⁿ A′ ⇒ B
forall-permutation-path-arrow-left path-refl = path-refl
forall-permutation-path-arrow-left (path-step step rest) =
  path-step (element-arrow-left step)
    (forall-permutation-path-arrow-left rest)

forall-permutation-path-arrow-right :
  ∀ {A B B′} →
  B ≈∀ⁿ B′ →
  A ⇒ B ≈∀ⁿ A ⇒ B′
forall-permutation-path-arrow-right path-refl = path-refl
forall-permutation-path-arrow-right (path-step step rest) =
  path-step (element-arrow-right step)
    (forall-permutation-path-arrow-right rest)

forall-permutation-path-all :
  ∀ {A B} →
  A ≈∀ⁿ B →
  `∀ A ≈∀ⁿ `∀ B
forall-permutation-path-all path-refl = path-refl
forall-permutation-path-all (path-step step rest) =
  path-step (element-all step)
    (forall-permutation-path-all rest)

normalize-forall-permutation :
  ∀ {A B} →
  A ≈∀ B →
  A ≈∀ⁿ B
normalize-forall-permutation ≈∀-refl = path-refl
normalize-forall-permutation (≈∀-sym A≈B) =
  forall-permutation-path-sym (normalize-forall-permutation A≈B)
normalize-forall-permutation (≈∀-trans A≈B B≈C) =
  forall-permutation-path-trans
    (normalize-forall-permutation A≈B)
    (normalize-forall-permutation B≈C)
normalize-forall-permutation (≈∀-⇒ A≈A′ B≈B′) =
  forall-permutation-path-trans
    (forall-permutation-path-arrow-left
      (normalize-forall-permutation A≈A′))
    (forall-permutation-path-arrow-right
      (normalize-forall-permutation B≈B′))
normalize-forall-permutation (≈∀-∀ A≈B) =
  forall-permutation-path-all (normalize-forall-permutation A≈B)
normalize-forall-permutation ≈∀-swap =
  path-step element-swap path-refl


WorldCoherentQuotientRepresentativeInstPathCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B D D′ C C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {sU sU′ : ImprecisionShape}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {D≈C : D ≈∀ C}
    {C⊑C′ : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {C′≈D′ : C′ ≈∀ D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (sourcePath : D ≈∀ⁿ C) →
  (targetPath : C′ ≈∀ⁿ D′) →
  normalize-forall-permutation D≈C ≡ sourcePath →
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
