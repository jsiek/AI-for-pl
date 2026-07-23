module
  proof.PairedLambda.Continuation.Frames.NuImprecisionPairedLambdaTargetClosingContinuationUpGenLeafDef
  where

-- File Charter:
--   * Defines the complete paired generic-upcast continuation leaf.
--   * Restates the terminal handler contract at its own dependency boundary.
--   * Contains no implementation, postulate, hole, permissive option, record
--     projection, or broad simulation import.

import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; `∀
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationUpGenLeafᵀ : Set₁
PairedLambdaTargetClosingContinuationUpGenLeafᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {X C′ D D′ B B′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ X ⊑ C′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  Value M → No• M →
  Value M′ → No• M′ →
  Inert d′ → Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.gen X d ∶ X ⊒ `∀ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ D′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pC →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)
    ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q
