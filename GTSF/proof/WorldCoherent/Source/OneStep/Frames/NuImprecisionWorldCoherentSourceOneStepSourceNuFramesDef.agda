module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  where

-- File Charter:
--   * Defines matched and source-only reveal-ν frames for a completed source
--     step.
--   * Every field consumes and returns the existing complete continuing
--     result directly; the recursive join lifts source blame separately.
--   * Contains no implementation, outcome wrapper, result alias, recursion,
--     postulate, hole, permissive option, or compatibility shim.

open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
import CastImprecisionShape as CastShape
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; ν)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; occurs; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)


record WorldCoherentSourceOneStepSourceNuFrames : Set₁ where
  field
    sourceStepMatchedNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L : Term} {A A′ B B′ C C′ : Ty}
        {s s′ : Coercion} {μ μ′} {χ : StoreChange}
        {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν A N s} {M′ = ν A′ N′ s′}
        {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

    sourceStepSourceNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L : Term} {A B B′ C : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {occ : occurs zero C ≡ true}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      {{safe : NonVar C}} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WfTy Δᴸ A →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺}
        (ν safe occ q) →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν A N s} {M′ = N′}
        {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

open WorldCoherentSourceOneStepSourceNuFrames public
