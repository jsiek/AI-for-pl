module proof.Quotient.NuImprecisionQuotientInstView where

-- File Charter:
--   * Freezes the structural view shared by the ordinary-down and general-
--     down quotient-instantiation residuals in recursive value catch-up.
--   * Combines only facts independently supplied by the quotiented endpoint
--     and the paired widening spine: a source-universal endpoint, usable cast
--     modes and typings, and the existing universal-imprecision view.
--   * Does not identify quotient representatives with coercion bodies; no
--     such connection follows from the current quotiented relation.
--   * Owns only the statement boundary.  Its proof is a low-risk leaf task.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; ∃-syntax)

import Coercions as C
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_; _≈∀_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; widen-mode-relax)
import NarrowWiden as NW
open import proof.Core.Permutation.ForallPermutationProperties using
  (AllImprecisionView; ⊑ᵖ-source-all-view)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ; seal★-tag-or-id)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-id-widening
  ; quotient-cast-widening
  )
open import TermTyping using
  (CastMode; SealModeStore★; cast-tag-or-id)
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
         ∃[ p ]
           (AllImprecisionView
             {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = Cᵖ}
             {B = Dᵖ} p ×
            (Dᵖ ≈∀ D′)))
quotient-inst-spine-viewᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {D′ = D′} qD
    (quotient-id-widening
      (C.cast-inst {A = C₀} hB occ s⊢ , NW.inst sʷ) u′⊑)
    with ⊑ᵖ-source-all-view
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = C₀} {B = D′} qD
quotient-inst-spine-viewᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {D′ = D′} qD
    (quotient-id-widening
      (C.cast-inst {A = C₀} hB occ s⊢ , NW.inst sʷ) u′⊑)
    | Cᵖ , Dᵖ , C≈Cᵖ , p , view , Dᵖ≈D′ =
  C₀ , refl , refl ,
  C.tag-or-idᵈ , C.tag-or-idᵈ ,
  cast-tag-or-id , seal★-tag-or-id ,
  widen-mode-relax C.id-only≤tag-or-idᵈ
    (C.cast-inst hB occ s⊢ , NW.inst sʷ) ,
  cast-tag-or-id , seal★-tag-or-id ,
  widen-mode-relax C.id-only≤tag-or-idᵈ u′⊑ ,
  Cᵖ , Dᵖ , C≈Cᵖ , p , view , Dᵖ≈D′
quotient-inst-spine-viewᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {D′ = D′} qD
    (quotient-cast-widening {μ = μ} {μ′ = μ′}
      mode seal★
      (C.cast-inst {A = C₀} hB occ s⊢ , NW.inst sʷ)
      mode′ seal★′ u′⊑)
    with ⊑ᵖ-source-all-view
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = C₀} {B = D′} qD
quotient-inst-spine-viewᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {D′ = D′} qD
    (quotient-cast-widening {μ = μ} {μ′ = μ′}
      mode seal★
      (C.cast-inst {A = C₀} hB occ s⊢ , NW.inst sʷ)
      mode′ seal★′ u′⊑)
    | Cᵖ , Dᵖ , C≈Cᵖ , p , view , Dᵖ≈D′ =
  C₀ , refl , refl ,
  μ , μ′ ,
  mode , seal★ , (C.cast-inst hB occ s⊢ , NW.inst sʷ) ,
  mode′ , seal★′ , u′⊑ ,
  Cᵖ , Dᵖ , C≈Cᵖ , p , view , Dᵖ≈D′
