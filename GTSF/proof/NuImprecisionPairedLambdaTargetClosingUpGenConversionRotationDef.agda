module
  proof.NuImprecisionPairedLambdaTargetClosingUpGenConversionRotationDef
  where

-- File Charter:
--   * Defines the quotient gen-down/gen conversion rotation required by
--     source-only allocation with an unchanged closed target value.
--   * Reconstructs the whole quotient leaf below the allocated runtime
--     bullet and moves the source body coercion below that bullet while
--     retaining the whole target coercion outside the target value.
--   * Stops before the final source reveal so the rotation is independent of
--     the closing result type.
--   * Contains no implementation, postulate, hole, or permissive option.

import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (∃-syntax)
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
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; ⇑ᵗ
  )


PairedLambdaTargetClosingUpGenConversionRotationᵀ : Set₁
PairedLambdaTargetClosingUpGenConversionRotationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {M M′ : Term} {X X′ D D′ B B′ Aν E C′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {d d′ u u′ c c′ : Coercion}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
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
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′} s (∀ⁱ q) →
  ∃[ r ]
    (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν ∣ []
      ⊢ᴺ
        ((⇑ᵗᵐ ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)) •) ⟨ c ⟩
        ⊑ ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) ⟨ c′ ⟩
        ⦂ `∀ E ⊑ `∀ C′ ∶ r)
