module PairedWideningCompatibility where

-- File Charter:
--   * Defines compatibility between paired source and target widenings.
--   * Keeps inert source casts and requires a source-output/target-input
--     bridge, together with both exact composition triangles, whenever an
--     active source is paired with an inert target.
--   * Contains no cast typing, term imprecision, or simulation proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; Inert)
open import Data.Product using (Σ; _×_; _,_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx)


data PairedWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (c c′ : Coercion) {A A′ B B′ : Ty}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
    (c-shape c′-shape : ImprecisionShape) : Set where
  compatible-source-inert :
    Inert c →
    PairedWideningCompatible
      Φ Δᴸ Δᴿ c c′ p q c-shape c′-shape

  compatible-target-inert-bridge :
    (Inert c′ →
      Σ (Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) λ bridge →
        (c-shape ； ⌊ bridge ⌋ ≋ ⌊ p ⌋) ×
        (⌊ bridge ⌋ ； c′-shape ≋ ⌊ q ⌋)) →
    PairedWideningCompatible
      Φ Δᴸ Δᴿ c c′ p q c-shape c′-shape


paired-widening-compatible-shape-transport :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q q′ : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {c-shape c′-shape : ImprecisionShape} →
  ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
  ⌊ q′ ⌋ ≡ ⌊ q ⌋ →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ c c′
    {A} {A′} {B} {B′} p q c-shape c′-shape →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ p′ q′ c-shape c′-shape
paired-widening-compatible-shape-transport
    p-shape q-shape (compatible-source-inert inert) =
  compatible-source-inert inert
paired-widening-compatible-shape-transport
    p-shape q-shape
    (compatible-target-inert-bridge bridge-evidence) =
  compatible-target-inert-bridge λ inert′ →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence inert′
    in
      bridge ,
      transport-result p-shape source-triangle ,
      transport-result q-shape target-triangle
  where
  transport-result :
    ∀ {s t r r′} →
    r′ ≡ r →
    s ； t ≋ r →
    s ； t ≋ r′
  transport-result refl comp = comp
