module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  where

-- File Charter:
--   * Defines identity-representative quotient-inst catch-up for the paired
--     universal case with generated downcasts.
--   * Exposes the inner ordinary term relation and both generated downcasts.
--   * Contains no implementation, quotient elimination, or dispatcher.

import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; `∀)
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
    {ρ : StoreImp Φ Δᴸ Δᴿ}
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
  C.genᵈ C.tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ `∀ E →
  C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ `∀ F →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (`∀ E) (`∀ F) A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
