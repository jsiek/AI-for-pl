module
  proof.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameClosingDef
  where

-- File Charter:
--   * Defines fused target closing through one quotient up-gen-all frame.
--   * Retains the recursively closed inner result expanded inline, its exact
--     proof-relevant frame view, inert target coercions, both gen tag-or-id
--     narrowing typings, the forall-permutation proof, the whole quotient
--     widening pair, the outer precision index, and the final structural
--     reveal interaction.
--   * Exposes no pre-reveal quotient-rotation intermediate.
--   * Contains no handler import, implementation, postulate, hole,
--     permissive option, recursive frame-closing dependency, or broad
--     simulation import.

import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using (Term; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)


PairedLambdaTargetClosingUpGenAllFrameClosingᵀ : Set₁
PairedLambdaTargetClosingUpGenAllFrameClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D₀ D₀′ B₀ B₀′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  (∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
      {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
    StoreImpPrefix ρ₀ ρ →
    (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
    RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
      (⟰ᵗ (leftStoreⁱ
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
      (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
      (renameᵗ (extᵗ suc) D) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
      {`∀ C} {C′} {`∀ (`∀ E)} {`∀ C₀′} pC (∀ⁱ s) →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
      ⊢ᴺ (((⇑ᵗᵐ M) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
        ⊑ M′ ⟨ c′ ⟩
        ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p) →
  PairedLambdaTargetClosingFrameView ρ₀ M M′ (`∀ C) C′ pC →
  Inert d′ → Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D₀ →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ C′ ⊒ D₀′ →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D₀ ⊑ᵖ D₀′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ₀
    (C.`∀ u) u′ (`∀ D₀) D₀′ (`∀ B₀) B₀′ →
  (q : Φ ∣ Δᴸ ⊢ `∀ B₀ ⊑ B₀′ ⊣ Δᴿ) →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B₀} {B₀′} {`∀ (`∀ E)} {`∀ C₀′} q (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p
