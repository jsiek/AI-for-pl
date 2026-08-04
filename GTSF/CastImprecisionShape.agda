module CastImprecisionShape where

-- File Charter:
--   * Defines hereditary imprecision shapes for narrowing and widening
--     coercions directly from coercion syntax.
--   * Retains nested universal and instantiation structure without retaining
--     proof-relevant assumption-membership or store witnesses.
--   * Contains no cast typing, term imprecision, or simulation proof.

open import Coercions using
  ( Coercion
  ; id
  ; _︔_
  ; _↦_
  ; `∀
  ; _!
  ; _？
  ; seal
  ; unseal
  ; gen
  ; inst
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; id★ˢ
  ; idˣˢ
  ; idιˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tagιˢ
  ; tag_⇛ˢ_
  ; tagˣˢ
  ; νˢ_
  ; _；_≋_
  )
open import Types using
  ( ★
  ; _⇒_
  ; ＇_
  ; ‵_
  )


data CastDirection : Set where
  narrowing : CastDirection
  widening : CastDirection


opposite : CastDirection → CastDirection
opposite narrowing = widening
opposite widening = narrowing


infix 4 _⊢ᶜ_⦂_

data _⊢ᶜ_⦂_ :
    CastDirection →
    Coercion →
    ImprecisionShape →
    Set where

  shape-id-var :
    ∀ {direction α} →
    direction ⊢ᶜ id (＇ α) ⦂ idˣˢ

  shape-id-base :
    ∀ {direction ι} →
    direction ⊢ᶜ id (‵ ι) ⦂ idιˢ

  shape-id-star :
    ∀ {direction} →
    direction ⊢ᶜ id ★ ⦂ id★ˢ

  shape-fun :
    ∀ {direction c d p q} →
    opposite direction ⊢ᶜ c ⦂ p →
    direction ⊢ᶜ d ⦂ q →
    direction ⊢ᶜ c ↦ d ⦂ p ↦ˢ q

  shape-all :
    ∀ {direction c p} →
    direction ⊢ᶜ c ⦂ p →
    direction ⊢ᶜ `∀ c ⦂ ∀ˢ p

  shape-tag-var :
    ∀ {α} →
    widening ⊢ᶜ (＇ α) ! ⦂ tagˣˢ

  shape-tag-base :
    ∀ {ι} →
    widening ⊢ᶜ (‵ ι) ! ⦂ tagιˢ

  shape-tag-fun :
    widening ⊢ᶜ (★ ⇒ ★) ! ⦂ tag id★ˢ ⇛ˢ id★ˢ

  shape-untag-var :
    ∀ {α} →
    narrowing ⊢ᶜ (＇ α) ？ ⦂ tagˣˢ

  shape-untag-base :
    ∀ {ι} →
    narrowing ⊢ᶜ (‵ ι) ？ ⦂ tagιˢ

  shape-untag-fun :
    narrowing ⊢ᶜ (★ ⇒ ★) ？ ⦂ tag id★ˢ ⇛ˢ id★ˢ

  shape-seal :
    ∀ {A α} →
    narrowing ⊢ᶜ seal A α ⦂ tagˣˢ

  shape-unseal :
    ∀ {α A} →
    widening ⊢ᶜ unseal α A ⦂ tagˣˢ

  shape-gen :
    ∀ {A c p} →
    narrowing ⊢ᶜ c ⦂ p →
    narrowing ⊢ᶜ gen A c ⦂ νˢ p

  shape-inst :
    ∀ {B c p} →
    widening ⊢ᶜ c ⦂ p →
    widening ⊢ᶜ inst B c ⦂ νˢ p

  shape-sequence-widening :
    ∀ {c d p q r} →
    widening ⊢ᶜ c ⦂ p →
    widening ⊢ᶜ d ⦂ q →
    p ； q ≋ r →
    widening ⊢ᶜ c ︔ d ⦂ r

  shape-sequence-narrowing :
    ∀ {c d p q r} →
    narrowing ⊢ᶜ c ⦂ p →
    narrowing ⊢ᶜ d ⦂ q →
    q ； p ≋ r →
    narrowing ⊢ᶜ c ︔ d ⦂ r
