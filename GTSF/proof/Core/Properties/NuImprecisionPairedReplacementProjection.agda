module
  proof.Core.Properties.NuImprecisionPairedReplacementProjection
  where

-- File Charter:
--   * Projects paired hereditary replacement to right hereditary replacement
--     when the source endpoint is unchanged.
--   * Supplies the exact premise required after a source identity conversion
--     in paired reveal and conceal catch-up.
--   * Contains no endpoint transport, postulate, hole, or permissive option.

open import ConversionIndexCompatibility using
  ( _[_↦_]ᴿ_
  ; _[_↦_⊑⟨_⟩_↤_]ᴾ_
  ; replace-paired-function
  ; replace-paired-function-tag
  ; replace-paired-idι
  ; replace-paired-idˣ
  ; replace-paired-id★
  ; replace-paired-tag
  ; replace-paired-tagˣ
  ; replace-paired-variables
  ; replace-paired-ν
  ; replace-paired-∀
  ; replace-right-function
  ; replace-right-function-tag
  ; replace-right-idι
  ; replace-right-idˣ
  ; replace-right-id★
  ; replace-right-tag
  ; replace-right-tagˣ
  ; replace-right-variable
  ; replace-right-ν
  ; replace-right-∀
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx; TyVar)


paired-replacement-same-source→right :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A A′ B′ X X′ : Ty} {α β : TyVar}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  p [ β ↦ X′ ]ᴿ q
paired-replacement-same-source→right replace-paired-id★ =
  replace-right-id★
paired-replacement-same-source→right replace-paired-idˣ =
  replace-right-idˣ
paired-replacement-same-source→right
    {q = q} (replace-paired-variables shape) =
  replace-right-variable q
paired-replacement-same-source→right replace-paired-idι =
  replace-right-idι
paired-replacement-same-source→right
    (replace-paired-function replacement₁ replacement₂) =
  replace-right-function
    (paired-replacement-same-source→right replacement₁)
    (paired-replacement-same-source→right replacement₂)
paired-replacement-same-source→right
    (replace-paired-∀ replacement) =
  replace-right-∀
    (paired-replacement-same-source→right replacement)
paired-replacement-same-source→right replace-paired-tag =
  replace-right-tag
paired-replacement-same-source→right
    (replace-paired-function-tag replacement₁ replacement₂) =
  replace-right-function-tag
    (paired-replacement-same-source→right replacement₁)
    (paired-replacement-same-source→right replacement₂)
paired-replacement-same-source→right replace-paired-tagˣ =
  replace-right-tagˣ
paired-replacement-same-source→right
    (replace-paired-ν replacement) =
  replace-right-ν
    (paired-replacement-same-source→right replacement)
