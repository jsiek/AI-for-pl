module QuotientImprecisionCompatibility where

-- File Charter:
--   * Defines the canonical cast-mode and widening compatibility evidence at
--     the reduction-closed quotient boundary.
--   * Requires an inert source widening to be paired with an active target;
--     inert targets instead supply an exact intermediate imprecision bridge.
--   * Keeps these concepts independent of term imprecision and operational
--     simulation.

import Coercions as C
open import Coercions using
  (Coercion; Inert; ModeEnv; id-onlyᵈ)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ; _×_)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; quotientᵖ; ≈∀-refl)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _↦ˢ_
  ; ∀ˢ_
  ; _；_≋_
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  )
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  (Store; Ty; TyCtx; _⇒_; `∀)


data SpineCastMode (Σ : Store) : ModeEnv → Set where
  id-only↓ :
    SpineCastMode Σ id-onlyᵈ

  gradual↓ :
    ∀ {μ} →
    CastMode μ →
    SealModeStore★ μ Σ →
    SpineCastMode Σ μ


data ReductionClosedPairedWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (c c′ : Coercion) → {A A′ B B′ : Ty} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    (c-shape c′-shape : ImprecisionShape) → Set where

  compatible-tagᴿ :
    ∀ {c′ A A′ B B′ p q c-shape c′-shape} G →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ (G C.!) c′
      {A} {A′} {B} {B′} p q c-shape c′-shape

  compatible-functionᴿ :
    ∀ {c₁ c₂ c₁′ c₂′ A₁ A₁′ A₂ A₂′
      B₁ B₁′ B₂ B₂′
      p₁ p₂ q₁ q₂ c₁-shape c₂-shape c₁′-shape c₂′-shape} →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c₂ c₂′ p₂ q₂ c₂-shape c₂′-shape →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ
      (c₁ C.↦ c₂) (c₁′ C.↦ c₂′)
      {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
      {B₁ ⇒ B₂} {B₁′ ⇒ B₂′}
      (p₁ ↦ p₂) (q₁ ↦ q₂)
      (c₁-shape ↦ˢ c₂-shape) (c₁′-shape ↦ˢ c₂′-shape)

  compatible-allᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    ReductionClosedPairedWideningCompatible
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (suc Δᴸ) (suc Δᴿ)
      c c′ p q c-shape c′-shape →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ
      (C.`∀ c) (C.`∀ c′)
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
      (∀ⁱ p) (∀ⁱ q) (∀ˢ c-shape) (∀ˢ c′-shape)

  compatible-target-activeᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    Inert c →
    (Inert c′ → ⊥) →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′
      {A} {A′} {B} {B′} p q c-shape c′-shape

  compatible-target-inert-bridgeᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    (Inert c′ →
      Σ (Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) (λ bridge →
      (c-shape ； ⌊ bridge ⌋ ≋ ⌊ p ⌋) ×
      (⌊ bridge ⌋ ； c′-shape ≋ ⌊ q ⌋))) →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′
      {A} {A′} {B} {B′} p q c-shape c′-shape


data ReductionClosedQuotientWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (u u′ : Coercion) → {D D′ A A′ : Ty} →
    (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    ImprecisionShape → ImprecisionShape → Set where

  compatible-through-representativesᴿ :
    ∀ {u u′ D D′ A A′ C C′ r p s s′ t t′}
      {src : D ForallPermutation.≈∀ C}
      {tgt : C′ ForallPermutation.≈∀ D′} →
    src ⊢ s ≈∀ˢ t →
    tgt ⊢ t′ ≈∀ˢ s′ →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ u u′
      {C} {C′} {A} {A′} r p t t′ →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′
      (quotientᵖ src r tgt) p s s′


reduction-closed-exact-widening-compatible :
  ∀ {Φ Δᴸ Δᴿ u u′ D D′ A A′ r p s s′} →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ u u′
    {D} {D′} {A} {A′} r p s s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′
    (quotientᵖ ≈∀-refl r ≈∀-refl) p s s′
reduction-closed-exact-widening-compatible compatible =
  compatible-through-representativesᴿ
    {src = ≈∀-refl} {tgt = ≈∀-refl}
    source-perm-refl source-perm-refl compatible
