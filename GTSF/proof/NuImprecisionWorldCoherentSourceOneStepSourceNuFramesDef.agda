module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  where

-- File Charter:
--   * Defines matched and source-only ordinary/casted source-ν frames for a
--     completed source step.
--   * Every field consumes and returns the existing complete continuing
--     result directly; the recursive join lifts source blame separately.
--   * Contains no implementation, outcome wrapper, result alias, recursion,
--     postulate, hole, permissive option, or compatibility shim.

open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  )
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
open import Types using (Ty; TyCtx; WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


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
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν A N s} {M′ = ν A′ N′ s′}
        {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

    sourceStepMatchedNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L : Term} {B B′ C C′ : Ty}
        {s s′ : Coercion} {μ μ′} {χ : StoreChange}
        {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      CastMode μ′ →
      SealModeStore★ (instᵈ μ′)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
      instᵈ μ′ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)
        ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
      PairedWideningCompatible
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) s s′ (⇑ᵗ B) C′ →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν ★ N s} {M′ = ν ★ N′ s′}
        {L = ν (applyTy χ ★) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

    sourceStepSourceNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L : Term} {A B B′ C : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WfTy Δᴸ A →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺} q →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν A N s} {M′ = N′}
        {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

    sourceStepSourceNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L : Term} {B B′ C : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      WorldCoherentSourceOneStepIndexedResult
        {M = N} {M′ = N′} {L = L}
        {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺} q →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν ★ N s} {M′ = N′}
        {L = ν (applyTy χ ★) L (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB

open WorldCoherentSourceOneStepSourceNuFrames public
