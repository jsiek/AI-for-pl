module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  where

-- File Charter:
--   * Defines the remaining general-cast widening branch of paired,
--     ordinary-down identity-representative quotient-inst catch-up.
--   * Exposes both widening modes because the source mode may require
--     ambient variable-to-star compatibility not present in the outer index.
--   * Contains no implementation, identity-mode branch, or dispatcher.

import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; `∀)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ :
  Set₁
WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B C C′ E F A A′ : Ty} {d d′ s u′ : C.Coercion}
    {μ μ′ : C.ModeEnv} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ E ⊑ F ⊣ suc Δᴿ →
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
  C.id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ `∀ E →
  C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ `∀ F →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ C.inst B s ∶ `∀ E ⊑ A →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ `∀ F ⊑ A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
