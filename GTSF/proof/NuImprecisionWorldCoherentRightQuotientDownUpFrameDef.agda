module proof.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef where

-- File Charter:
--   * Defines the two world-coherent right quotient down/up frame cases.
--   * Keeps identity-mode and generated-mode downcasts separate while
--     sharing the canonical recursive and framed-result boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Data.List using ([])

open import Coercions using
  (Coercion; Inert; genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightQuotientDownUpFrame : Set₁ where
  field
    rightQuotientIdDownUpFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ D D′ A A′ : Ty}
        {d d′ u u′ : Coercion}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
      Value M →
      No• M →
      Inert d →
      Inert u →
      id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} pC →
      WorldCoherentRightValueCatchupIndexedResult
        {V = (M ⟨ d ⟩) ⟨ u ⟩}
        {M′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩} {ρ = ρ⁺} pA

    rightQuotientGenDownUpFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ D D′ A A′ : Ty}
        {d d′ u u′ : Coercion}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
      Value M →
      No• M →
      Inert d →
      Inert u →
      genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
        ⊢ d ∶ C ⊒ D →
      genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} pC →
      WorldCoherentRightValueCatchupIndexedResult
        {V = (M ⟨ d ⟩) ⟨ u ⟩}
        {M′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩} {ρ = ρ⁺} pA

open WorldCoherentRightQuotientDownUpFrame public
