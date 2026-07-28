module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesDef
  where

-- File Charter:
--   * Defines matched and source-only reveal-ν frames around a
--     target-oriented world-coherent one-step simulation.
--   * Retains exact lifted replacements.
--   * Contains no implementation, active allocation root, recursion,
--     postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
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
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; ν)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; occurs
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepNuFrames : Set₁ where
  field
    rightStepMatchedNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {A A′ B B′ C C′ : Ty}
        {s s′ : Coercion} {μ μ′} {χ : StoreChange}
        {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = `∀ C} {B = `∀ C′}
        {χ = χ} {ρ = ρ} (∀ⁱ q) →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν A N s}
        {N′ = ν (applyTy χ A′) N₁′
          (applyCoercionUnderTyBinder χ s′)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    rightStepSourceNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {A B B′ C : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {occ : occurs zero C ≡ true}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      {{safe : NonVar C}} →
      WfTy Δᴸ A →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = `∀ C} {B = B′}
        {χ = χ} {ρ = ρ} (ν safe occ q) →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν A N s} {N′ = N₁′}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

open WorldCoherentRightOneStepNuFrames public
