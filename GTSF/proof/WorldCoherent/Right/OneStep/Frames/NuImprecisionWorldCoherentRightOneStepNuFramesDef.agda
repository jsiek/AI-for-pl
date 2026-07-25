module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesDef
  where

-- File Charter:
--   * Defines matched, source-only, and target-only ordinary/casted ν frames
--     around a target-oriented world-coherent one-step simulation.
--   * Retains exact lifted replacements, cast shapes, composition triangles,
--     and paired widening compatibility.
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
open import NuTermImprecision using
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

    rightStepMatchedNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {B B′ C C′ : Ty}
        {s s′ : Coercion} {μ μ′} {χ : StoreChange}
        {s-shape s′-shape result-shape : ImprecisionShape}
        {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      CastMode μ′ →
      SealModeStore★ (instᵈ μ′)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
      instᵈ μ′ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      CastShape.widening CastShape.⊢ᶜ s′ ⦂ s′-shape →
      s-shape ； ⌊ pB ⌋ ≋ result-shape →
      ⌊ q ⌋ ； s′-shape ≋ result-shape →
      PairedWideningCompatible
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) s s′
        q (⊑-lift∀ᵢ pB) s-shape s′-shape →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = `∀ C} {B = `∀ C′}
        {χ = χ} {ρ = ρ} (∀ⁱ q) →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν ★ N s}
        {N′ = ν ★ N₁′ (applyCoercionUnderTyBinder χ s′)}
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

    rightStepSourceNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {B B′ C : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {s-shape : ImprecisionShape}
        {occ : occurs zero C ≡ true}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      {{safe : NonVar C}} →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      s-shape ； ⌊ pB ⌋ ≋ ⌊ q ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = `∀ C} {B = B′}
        {χ = χ} {ρ = ρ} (ν safe occ q) →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν ★ N s} {N′ = N₁′}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    rightStepTargetNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {A B B′ C′ : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      WfTy Δᴿ A →
      RevealConversion μ (suc Δᴿ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      r [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = B} {B = `∀ C′}
        {χ = χ} {ρ = ρ} q →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N}
        {N′ = ν (applyTy χ A) N₁′
          (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    rightStepTargetNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N₁′ : Term} {B B′ C′ : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {s-shape : ImprecisionShape}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
      instᵈ μ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      ⌊ r ⌋ ； s-shape ≋ ⌊ pB ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N₁′} {A = B} {B = `∀ C′}
        {χ = χ} {ρ = ρ} q →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N}
        {N′ = ν ★ N₁′ (applyCoercionUnderTyBinder χ s)}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

open WorldCoherentRightOneStepNuFrames public
