{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionQuotientInstView where

-- File Charter:
--   * Freezes the structural view shared by the ordinary-down and general-
--     down quotient-instantiation residuals in recursive value catch-up.
--   * Combines only facts independently supplied by the quotiented endpoint
--     and the paired widening spine: a source-universal endpoint, usable cast
--     modes and typings, and the existing universal-imprecision view.
--   * Does not identify quotient representatives with coercion bodies; no
--     such connection follows from the current quotiented relation.
--   * Owns only the statement boundary.  Its proof is a low-risk leaf task.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; ∃-syntax)

import Coercions as C
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_; _≈∀_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import proof.ForallPermutationProperties using
  (AllImprecisionView)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import QuotientedTermImprecision using
  (QuotientWideningPair)
open import TermTyping using
  (CastMode; SealModeStore★)
import Types as T


quotient-inst-spine-viewᵀ :
  ∀ {Φ Δᴸ Δᴿ B s u′ D D′ A A′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ D D′ A A′ →
  ∃[ C ]
    (D ≡ T.`∀ C) ×
    (A ≡ B) ×
    ∃[ μ ] ∃[ μ′ ]
      CastMode μ ×
      SealModeStore★ μ (leftStoreⁱ ρ) ×
      (μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.inst B s ∶ T.`∀ C ⊑ B) ×
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ u′ ∶ D′ ⊑ A′) ×
      ∃[ Cᵖ ] ∃[ Dᵖ ]
        ((T.`∀ C ≈∀ T.`∀ Cᵖ) ×
         ∃[ p ] (AllImprecisionView p × (Dᵖ ≈∀ D′)))
quotient-inst-spine-viewᵀ = {!!}
