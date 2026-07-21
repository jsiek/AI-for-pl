module
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  where

-- File Charter:
--   * Defines the structural core of the matched-`Λ`/`Λ` paired-reveal
--     closing branch after both universal reveal conversions are inverted.
--   * Retains the matched body relation, source allocation, conversion
--     correspondence, result imprecision index, both inner reveals, and final
--     reveal as one fused step.
--   * Exposes no pre-final-reveal source-only intermediate index.
--   * Contains no implementation, postulate, hole, permissive option, broad
--     simulation import, or recursive frame closer.

import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
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


PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ :
  Set₁
PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρΛ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γΛ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {A B : Ty}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρΛ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γΛ →
  Value V → No• V → Value V′ → No• V′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρΛ ∣ γΛ
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ r →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {Aν C′ D E X X′ : Ty} {c c′ t : Coercion}
    {η η′ μ : ModeEnv} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ Aν)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
    (suc α) (⇑ᵗ X) c A (`∀ E) →
  RevealConversion (C.extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
    (suc β) (⇑ᵗ X′) c′ B C′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (Λ V)) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ (Λ V′) ⟨ C.`∀ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
