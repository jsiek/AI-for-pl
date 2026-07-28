module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupDef
  where

-- File Charter:
--   * Defines the paired `∀`/`∀` semantic branch of identity-path
--     representative-inst catch-up.
--   * Keeps the lifted body-imprecision witness and both original
--     self-permutation derivations explicit.
--   * Contains no implementation or recursive simulation dependency.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionWf using
  (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_; ∀ⁱ_)
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
open import Types using (Ty; `∀)
open import proof.Core.Permutation.ForallPermutationPath
  using (normalize-forall-permutation; path-refl)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term} {B E F A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {sU sU′ : ImprecisionShape}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {E≈E : `∀ E ≈∀ `∀ E}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ E ⊑ F ⊣ suc Δᴿ}
    {F≈F : `∀ F ≈∀ `∀ F}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  normalize-forall-permutation E≈E ≡ path-refl →
  normalize-forall-permutation F≈F ≡ path-refl →
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
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ `∀ E ⊑ᵖ `∀ F
      ∶ quotientᵖ E≈E (∀ⁱ r) F≈F →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (`∀ E) (`∀ F) A A′ →
  widening ⊢ᶜ C.inst B s ⦂ sU →
  widening ⊢ᶜ u′ ⦂ sU′ →
  sU ；⌊ pA ⌋≋ᵖ
    quotientᵖ E≈E (∀ⁱ r) F≈F ； sU′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
