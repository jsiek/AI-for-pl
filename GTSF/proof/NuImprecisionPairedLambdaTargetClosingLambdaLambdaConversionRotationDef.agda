module
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaConversionRotationDef
  where

-- File Charter:
--   * Defines the matched-`Λ`/`Λ` paired-conversion rotation required by
--     source-only allocation with a closed target binder.
--   * Moves the source body coercion below the allocated runtime bullet while
--     retaining the whole target coercion outside the target `Λ`.
--   * Stops before the final source reveal so the same rotation can support
--     both reveal and widening closing arguments.
--   * Contains no implementation, postulate, hole, or permissive option.

import Coercions as C
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (∃-syntax)
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
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
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
  ( PairedConversion
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


PairedLambdaTargetClosingLambdaLambdaConversionRotationᵀ : Set₁
PairedLambdaTargetClosingLambdaLambdaConversionRotationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ₀∀ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {Aν F F′ E C′ : Ty}
    {c c′ : Coercion}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ F ⊑ F′ ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₀∀ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γ₀∀ →
  Value V → No• V →
  Value V′ → No• V′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₀∀ ∣ γ₀∀
    ⊢ᴺ V ⊑ V′ ⦂ F ⊑ F′ ∶ r →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ F} {`∀ F′} {`∀ (`∀ E)} {`∀ C′}
    (∀ⁱ r) (∀ⁱ q) →
  ∃[ s ]
    (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν ∣ []
      ⊢ᴺ ((⇑ᵗᵐ (Λ V)) •) ⟨ c ⟩
        ⊑ (Λ V′) ⟨ c′ ⟩
        ⦂ `∀ E ⊑ `∀ C′ ∶ s)
