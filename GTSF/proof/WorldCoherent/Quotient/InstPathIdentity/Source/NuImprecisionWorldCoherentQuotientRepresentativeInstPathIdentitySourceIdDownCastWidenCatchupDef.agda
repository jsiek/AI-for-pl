module
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  where

-- File Charter:
--   * Defines the remaining general-cast widening branch of source-only,
--     ordinary-down identity-representative quotient-inst catch-up.
--   * Retains the non-vacuous `NonVar` and occurrence premises.
--   * Contains no implementation, identity-mode branch, or dispatcher.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; occurs; `∀)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ :
  Set₁
WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {B C C′ E T A A′ : Ty} {d d′ s u′ : C.Coercion}
    {μ μ′ : C.ModeEnv} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {{safe : NonVar E}}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (occ : occurs zero E ≡ true) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ⊢ E ⊑ T ⊣ Δᴿ →
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
  C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ T →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ C.inst B s ∶ `∀ E ⊑ A →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ T ⊑ A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
