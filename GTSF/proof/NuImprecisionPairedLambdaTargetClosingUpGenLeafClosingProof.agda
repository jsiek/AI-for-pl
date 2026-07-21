module
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingProof
  where

-- File Charter:
--   * Adapts the quotient gen-down/gen conversion rotation theorem to the
--     complete concrete frame-closing leaf.
--   * Performs the final structural universal reveal after the rotated
--     source body cast and retains the whole target coercion unchanged.
--   * Exposes the unavailable rotation theorem as one higher-order parameter.
--   * Contains no implementation of rotation, postulate, hole, or permissive
--     option.

import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Conversion using (RevealConversion; reveal-all)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
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
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedConversion
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; conv↑⊑ᵀ
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
  proof.NuImprecisionPairedLambdaTargetClosingUpGenConversionRotationDef
  using (PairedLambdaTargetClosingUpGenConversionRotationᵀ)


paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ :
  PairedLambdaTargetClosingUpGenConversionRotationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {X X′ D D′ B B′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  Value M → No• M →
  Value M′ → No• M′ →
  Inert d′ → Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ C.gen X d ∶ X ⊒ `∀ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ X′ ⊒ D′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ₀
    (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
  (s : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C′ Dᶠ E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ Dᶠ ⊑ `∀ C′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) Dᶠ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′} s (∀ⁱ q) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ Dᶠ) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
    rotation vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening s
    {p = p}
    prefix h⇑A reveal liftν lift∀ conversion
    with rotation prefix vM noM vM′ noM′ inert-d′ inert-u′
      d⊒ d′⊒ M⊑M′ qD widening s h⇑A liftν lift∀ conversion
paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
    rotation vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening s
    {p = p}
    prefix h⇑A reveal liftν lift∀ conversion
    | r , rotated =
  conv↑⊑ᵀ (reveal-all reveal) rotated (⊑-source-liftνᵢ p)
