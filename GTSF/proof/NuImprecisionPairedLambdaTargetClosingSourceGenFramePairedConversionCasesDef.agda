module
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesDef
  where

-- File Charter:
--   * Defines the exact reveal and conceal constructor branches required by
--     source-generic-frame target closing.
--   * Keeps the recursive closing result, source allocation, paired
--     conversion fields, and final reveal fused in each branch.
--   * Contains no dispatcher, implementation, postulate, hole, permissive
--     option, or broad simulation import.

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ : Set₁
PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V N′ : Term} {F B B′ A C′ D E X X′ : Ty}
    {g c c′ t : Coercion} {η η′ θ : ModeEnv}
    {α β : TyVar}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  Value V → No• V → Value N′ → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ `∀ F ⊑ `∀ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ C.gen (`∀ F) g ⟩ ⊑ N′
      ⦂ `∀ B ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀
    V N′ F (`∀ B′) q →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ θ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion η Δᴸ (leftStoreⁱ ρ) α X
    (C.`∀ c) (`∀ B) (`∀ (`∀ E)) →
  RevealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′
    c′ (`∀ B′) (`∀ C′) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (V ⟨ C.gen (`∀ F) g ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ N′ ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p


PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ : Set₁
PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V N′ : Term} {F B B′ A C′ D E X X′ : Ty}
    {g c c′ t : Coercion} {η η′ θ : ModeEnv}
    {α β : TyVar}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  Value V → No• V → Value N′ → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ `∀ F ⊑ `∀ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ C.gen (`∀ F) g ⟩ ⊑ N′
      ⦂ `∀ B ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀
    V N′ F (`∀ B′) q →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ θ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  StoreCorresponds ρ α X β X′ pX →
  ConcealConversion η Δᴸ (leftStoreⁱ ρ) α X
    (C.`∀ c) (`∀ B) (`∀ (`∀ E)) →
  ConcealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′
    c′ (`∀ B′) (`∀ C′) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (V ⟨ C.gen (`∀ F) g ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ N′ ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
