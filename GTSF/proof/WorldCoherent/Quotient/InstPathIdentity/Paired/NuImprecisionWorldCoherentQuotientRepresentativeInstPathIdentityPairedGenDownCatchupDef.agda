module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  where

-- File Charter:
--   * Defines identity-representative quotient-inst catch-up for the paired
--     universal case with generated downcasts.
--   * Exposes the inner ordinary term relation and both generated downcasts.
--   * Contains no implementation, quotient elimination, or dispatcher.

import Coercions as C
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_≈∀_; quotientᵖ)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
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


WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ :
  Set₁
WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B C C′ E F A A′ : Ty} {d d′ s u′ : C.Coercion}
    {sD sD′ sU sU′ : ImprecisionShape}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {E≈E : `∀ E ≈∀ `∀ E}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {F≈F : `∀ F ≈∀ `∀ F}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ E ⊑ F ⊣ suc Δᴿ) →
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
  C.genᵈ C.tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ `∀ E →
  narrowing ⊢ᶜ d ⦂ sD →
  C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ `∀ F →
  narrowing ⊢ᶜ d′ ⦂ sD′ →
  sD ；⌊ pC ⌋≋ᵖ
    quotientᵖ E≈E (∀ⁱ r) F≈F ； sD′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
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
