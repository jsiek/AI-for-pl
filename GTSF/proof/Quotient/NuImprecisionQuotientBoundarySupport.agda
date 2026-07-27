module
  proof.Quotient.NuImprecisionQuotientBoundarySupport
  where

-- File Charter:
--   * Defines quotient-boundary evidence shared by experimental term
--     imprecision relations.
--   * Keeps cast-mode and hereditary widening compatibility independent of
--     every term-imprecision judgment.
--   * Contains no constructor that embeds or converts between term relations.

open import Coercions using (Coercion; ModeEnv; id-onlyᵈ)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; quotientᵖ; ≈∀-refl)
open import Imprecision using (ImpCtx)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Store; Ty; TyCtx)


data SpineCastMode (Σ : Store) : ModeEnv → Set where
  id-only↓ :
    SpineCastMode Σ id-onlyᵈ

  gradual↓ :
    ∀ {μ} →
    CastMode μ →
    SealModeStore★ μ Σ →
    SpineCastMode Σ μ


data QuotientWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (u u′ : Coercion) → {D D′ A A′ : Ty} →
    (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    ImprecisionShape → ImprecisionShape → Set where

  compatible-through-representatives :
    ∀ {u u′ D D′ A A′ C C′ r p s s′ t t′}
      {src : D ForallPermutation.≈∀ C}
      {tgt : C′ ForallPermutation.≈∀ D′} →
    src ⊢ s ≈∀ˢ t →
    tgt ⊢ t′ ≈∀ˢ s′ →
    PairedWideningCompatible Φ Δᴸ Δᴿ u u′
      {C} {C′} {A} {A′} r p t t′ →
    QuotientWideningCompatible Φ Δᴸ Δᴿ u u′
      (quotientᵖ src r tgt) p s s′


exact-widening-compatible :
  ∀ {Φ Δᴸ Δᴿ u u′ D D′ A A′ r p s s′} →
  PairedWideningCompatible Φ Δᴸ Δᴿ u u′
    {D} {D′} {A} {A′} r p s s′ →
  QuotientWideningCompatible Φ Δᴸ Δᴿ u u′
    (quotientᵖ ≈∀-refl r ≈∀-refl) p s s′
exact-widening-compatible compatible =
  compatible-through-representatives
    {src = ≈∀-refl} {tgt = ≈∀-refl}
    source-perm-refl source-perm-refl compatible
