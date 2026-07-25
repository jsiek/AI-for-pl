module
  proof.Quotient.NuImprecisionSourceDownApplicationCompatibleOuter
  where

-- File Charter:
--   * Shows that the source-down application residual can be rebuilt as
--     ordinary imprecision beneath an outer quotient widening exactly when
--     that widening carries `PairedWideningCompatible`.
--   * Extracts both ordinary composition triangles from the reflexive
--     quotient boundary square.
--   * Makes the sole missing compatibility premise explicit for the
--     source-down application beta obstruction.
--   * Contains no world-coherent result, reduction, postulate, hole,
--     permissive option, or compatibility wrapper.

import CastImprecisionShape as CastShape
open import Coercions using
  (Coercion; ModeEnv; id-only≤tag-or-idᵈ)
open import Data.List using ([])
open import ForallPermutation using
  (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using
  ( _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  ; ⌊_⌋
  ; quotient-boundary-square
  ; source-perm-refl
  )
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (widen-mode-relax; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; seal★-tag-or-id)
open import NuTerms using
  (Term; _·_; _⟨_⟩)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; cast⊒⊑ᵀ
  ; conv⊑convᵀ
  ; paired-widening
  ; quotient-cast-widening
  ; quotient-id-widening
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; cast-tag-or-id)
open import Types using (Ty; TyCtx; _⇒_)


source-down-application-compatible-outerᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ : Term}
    {X C C′ B B′ E E′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ C′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {d u u′ : Coercion}
    {μ : ModeEnv}
    {d-shape u-shape u′-shape} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ X ⊒ C →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pX →
  d-shape ； ⌊ pX ⌋ ≋ ⌊ pC ⌋ →
  (widening :
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ B B′ E E′) →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pE ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ u u′ pB pE u-shape u′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ (L · (M ⟨ d ⟩)) ⟨ u ⟩
      ⊑ (L′ · M′) ⟨ u′ ⟩
      ⦂ E ⊑ E′ ∶ pE
source-down-application-compatible-outerᵀ
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    (quotient-id-widening u⊑ u′⊑)
    u-shape u′-shape
    (quotient-boundary-square
      source-perm-refl source-composition
      source-perm-refl target-composition)
    compatible =
  conv⊑convᵀ
    (paired-widening
      cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u⊑)
      u-shape
      cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u′⊑)
      u′-shape
      source-composition target-composition compatible)
    application
  where
  argument =
    cast⊒⊑ᵀ mode seal★ d⊒ M⊑M′ _
      d-shape down-triangle

  application = ·⊑·ᵀ L⊑L′ argument
source-down-application-compatible-outerᵀ
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    (quotient-cast-widening
      mode-u seal★-u u⊑ mode-u′ seal★-u′ u′⊑)
    u-shape u′-shape
    (quotient-boundary-square
      source-perm-refl source-composition
      source-perm-refl target-composition)
    compatible =
  conv⊑convᵀ
    (paired-widening
      mode-u seal★-u u⊑ u-shape
      mode-u′ seal★-u′ u′⊑ u′-shape
      source-composition target-composition compatible)
    application
  where
  argument =
    cast⊒⊑ᵀ mode seal★ d⊒ M⊑M′ _
      d-shape down-triangle

  application = ·⊑·ᵀ L⊑L′ argument
