module
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupDef
  where

-- File Charter:
--   * Defines the source-only non-vacuous `ν` semantic branch of
--     identity-path representative-inst catch-up.
--   * Retains `NonVar`, occurrence, the lifted body relation, and both
--     original self-permutation derivations explicitly.
--   * Contains no implementation or recursive simulation dependency.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionWf using
  ( NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; occurs; `∀)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ : Set₁
WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term} {B E C′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {E≈E : `∀ E ≈∀ `∀ E}
    {{safe : NonVar E}}
    {occ : occurs zero E ≡ true}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ E ⊑ C′ ⊣ Δᴿ}
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
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ `∀ E ⊑ᵖ C′
      ∶ quotientᵖ E≈E (ν safe occ r) C′≈C′ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (`∀ E) C′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
