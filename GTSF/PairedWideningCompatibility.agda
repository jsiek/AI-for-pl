module PairedWideningCompatibility where

-- File Charter:
--   * Defines hereditary compatibility between paired source and target
--     widenings.
--   * Makes the residual compatibility exposed by function and universal
--     elimination available directly.
--   * Keeps source tags as terminal cases, separates active targets from
--     inert targets, and requires an exact bridge for the latter.
--   * Contains no cast typing, term imprecision, or simulation proof.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (Coercion; Inert)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _↦ˢ_
  ; ∀ˢ_
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; ∀ⁱ_
  )
open import Types using (Ty; TyCtx; _⇒_; `∀)


↦ˢ-right-injective :
  ∀ {p q p′ q′} →
  p ↦ˢ q ≡ p′ ↦ˢ q′ →
  q ≡ q′
↦ˢ-right-injective refl = refl


∀ˢ-injective :
  ∀ {p p′} →
  ∀ˢ p ≡ ∀ˢ p′ →
  p ≡ p′
∀ˢ-injective refl = refl


data PairedWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (c c′ : Coercion) → {A A′ B B′ : Ty} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    (c-shape c′-shape : ImprecisionShape) → Set where
  compatible-tag :
    ∀ {c′ : Coercion} {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {c-shape c′-shape : ImprecisionShape} G →
    PairedWideningCompatible
      Φ Δᴸ Δᴿ (G C.!) c′ p q c-shape c′-shape

  compatible-function :
    ∀ {c₁ c₂ c₁′ c₂′ A₁ A₁′ A₂ A₂′ B₁ B₁′ B₂ B₂′
      p₁ p₂ q₁ q₂ c₁-shape c₂-shape c₁′-shape c₂′-shape} →
    PairedWideningCompatible
      Φ Δᴸ Δᴿ c₂ c₂′ p₂ q₂ c₂-shape c₂′-shape →
    PairedWideningCompatible Φ Δᴸ Δᴿ
      (c₁ C.↦ c₂) (c₁′ C.↦ c₂′)
      {A₁ ⇒ A₂} {A₁′ ⇒ A₂′} {B₁ ⇒ B₂} {B₁′ ⇒ B₂′}
      (p₁ ↦ p₂) (q₁ ↦ q₂)
      (c₁-shape ↦ˢ c₂-shape) (c₁′-shape ↦ˢ c₂′-shape)

  compatible-all :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    PairedWideningCompatible
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (suc Δᴸ) (suc Δᴿ)
      c c′ p q c-shape c′-shape →
    PairedWideningCompatible Φ Δᴸ Δᴿ
      (C.`∀ c) (C.`∀ c′)
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
      (∀ⁱ p) (∀ⁱ q) (∀ˢ c-shape) (∀ˢ c′-shape)

  compatible-source-inert :
    ∀ {c c′ : Coercion} {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {c-shape c′-shape : ImprecisionShape} →
    Inert c →
    PairedWideningCompatible
      Φ Δᴸ Δᴿ c c′ p q c-shape c′-shape

  compatible-target-inert-bridge :
    ∀ {c c′ : Coercion} {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {c-shape c′-shape : ImprecisionShape} →
    (Inert c′ →
      Σ (Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) (λ bridge →
      (c-shape ； ⌊ bridge ⌋ ≋ ⌊ p ⌋) ×
      (⌊ bridge ⌋ ； c′-shape ≋ ⌊ q ⌋))) →
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
    p-shape q-shape (compatible-tag G) =
  compatible-tag G
paired-widening-compatible-shape-transport
    {p′ = p₁′ ↦ p₂′} {q′ = q₁′ ↦ q₂′}
    p-shape q-shape (compatible-function compatible) =
  compatible-function
    (paired-widening-compatible-shape-transport
      (↦ˢ-right-injective p-shape)
      (↦ˢ-right-injective q-shape)
      compatible)
paired-widening-compatible-shape-transport
    {p′ = ∀ⁱ p′} {q′ = ∀ⁱ q′}
    p-shape q-shape (compatible-all compatible) =
  compatible-all
    (paired-widening-compatible-shape-transport
      (∀ˢ-injective p-shape)
      (∀ˢ-injective q-shape)
      compatible)
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
      bridge
      , transport-result p-shape source-triangle
      , transport-result q-shape target-triangle
  where
  transport-result :
    ∀ {s t r r′} →
    r′ ≡ r →
    s ； t ≋ r →
    s ； t ≋ r′
  transport-result refl comp = comp
