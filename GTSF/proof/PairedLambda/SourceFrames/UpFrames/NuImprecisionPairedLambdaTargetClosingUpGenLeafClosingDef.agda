module
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingDef
  where

-- File Charter:
--   * Defines the fused closing contract for the terminal quotient
--     gen-down/gen value case.
--   * Retains the quotient narrowing relation, whole widening pair, external
--     paired conversion, source runtime-bullet allocation, and final
--     structural universal reveal in one semantic theorem.
--   * Exposes no pre-reveal quotient-rotation intermediate; that proposed
--     factorization is refuted by the checked impossible-index example.
--   * Contains no handler import, implementation, postulate, hole,
--     permissive option, or broad simulation import.

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
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)


PairedLambdaTargetClosingUpGenLeafClosingᵀ : Set₁
PairedLambdaTargetClosingUpGenLeafClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {X C₀′ D₀ D₀′ B₀ B₀′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ X ⊑ C₀′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  Value M → No• M →
  Value M′ → No• M′ →
  Inert d′ → Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ C.gen X d ∶ X ⊒ `∀ D₀ →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ C₀′ ⊒ D₀′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C₀′ ∶ pC →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D₀ ⊑ᵖ D₀′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ₀
    (C.`∀ u) u′ (`∀ D₀) D₀′ (`∀ B₀) B₀′ →
  (r : Φ ∣ Δᴸ ⊢ `∀ B₀ ⊑ B₀′ ⊣ Δᴿ) →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
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
    {`∀ B₀} {B₀′} {`∀ (`∀ E)} {`∀ C′} r (∀ⁱ q) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ
        ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
