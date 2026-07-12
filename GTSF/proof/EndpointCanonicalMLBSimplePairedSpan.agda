module proof.EndpointCanonicalMLBSimplePairedSpan where

-- File Charter:
--   * Defines the proof-only paired span context used by simple MLB
--     factorization.
--   * Records the two endpoint views of a common-lower variable in one row.
--   * Unifies the three variable terminal factorization arguments through a
--     single pullback property.
--   * Keeps the paired representation internal to the factorization proof.

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import Types
open import Imprecision using (ImpCtx; idᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_; id★; idˣ; idι; _↦_; ∀ⁱ_; tag_; tag_⇛_
  ; tagˣ; ν
  )
open import proof.EndpointCanonicalMLBSimple using (∀ᵢᶜ; νᵢᶜ)
open import proof.ImprecisionProperties using
  (idᵢ-no-star; idᵢ-var-identity)

data View : Set where
  varᵛ : TyVar → View
  ★ᵛ : View

record SpanCtx : Set where
  constructor span
  field
    left-context : ImpCtx
    right-context : ImpCtx

open SpanCtx

infix 4 _↦⟨_,_⟩∈_
data _↦⟨_,_⟩∈_ : TyVar → View → View → SpanCtx → Set where
  row-var-var :
    ∀ {Φᴸ Φᴿ Z X Y} →
    (Z ˣ⊑ˣ X) ∈ Φᴸ →
    (Z ˣ⊑ˣ Y) ∈ Φᴿ →
    Z ↦⟨ varᵛ X , varᵛ Y ⟩∈ span Φᴸ Φᴿ

  row-var-star :
    ∀ {Φᴸ Φᴿ Z X} →
    (Z ˣ⊑ˣ X) ∈ Φᴸ →
    (Z ˣ⊑★) ∈ Φᴿ →
    Z ↦⟨ varᵛ X , ★ᵛ ⟩∈ span Φᴸ Φᴿ

  row-star-var :
    ∀ {Φᴸ Φᴿ Z Y} →
    (Z ˣ⊑★) ∈ Φᴸ →
    (Z ˣ⊑ˣ Y) ∈ Φᴿ →
    Z ↦⟨ ★ᵛ , varᵛ Y ⟩∈ span Φᴸ Φᴿ

  row-star-star :
    ∀ {Φᴸ Φᴿ Z} →
    (Z ˣ⊑★) ∈ Φᴸ →
    (Z ˣ⊑★) ∈ Φᴿ →
    Z ↦⟨ ★ᵛ , ★ᵛ ⟩∈ span Φᴸ Φᴿ

data SpanExposure : Set where
  bothˢ : SpanExposure
  leftˢ : SpanExposure
  rightˢ : SpanExposure
  neitherˢ : SpanExposure

extend-span : SpanExposure → SpanCtx → SpanCtx
extend-span bothˢ (span Φᴸ Φᴿ) = span (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
extend-span leftˢ (span Φᴸ Φᴿ) = span (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
extend-span rightˢ (span Φᴸ Φᴿ) = span (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
extend-span neitherˢ (span Φᴸ Φᴿ) =
  span (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)

data PairedLower (Σ : SpanCtx) (Δᶜ : TyCtx) :
    Ty → Ty → Ty → TyCtx → TyCtx → Set where
  paired-star :
    ∀ {Δᴸ Δᴿ} →
    PairedLower Σ Δᶜ ★ ★ ★ Δᴸ Δᴿ

  paired-base-base :
    ∀ {Δᴸ Δᴿ ι} →
    PairedLower Σ Δᶜ (‵ ι) (‵ ι) (‵ ι) Δᴸ Δᴿ

  paired-base-star :
    ∀ {Δᴸ Δᴿ ι} →
    PairedLower Σ Δᶜ (‵ ι) (‵ ι) ★ Δᴸ Δᴿ

  paired-star-base :
    ∀ {Δᴸ Δᴿ ι} →
    PairedLower Σ Δᶜ (‵ ι) ★ (‵ ι) Δᴸ Δᴿ

  paired-base-stars :
    ∀ {Δᴸ Δᴿ ι} →
    PairedLower Σ Δᶜ (‵ ι) ★ ★ Δᴸ Δᴿ

  paired-arrow-arrow :
    ∀ {Δᴸ Δᴿ C₁ C₂ A₁ A₂ B₁ B₂} →
    PairedLower Σ Δᶜ C₁ A₁ B₁ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ C₂ A₂ B₂ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ
      (C₁ ⇒ C₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂) Δᴸ Δᴿ

  paired-arrow-star :
    ∀ {Δᴸ Δᴿ C₁ C₂ A₁ A₂} →
    PairedLower Σ Δᶜ C₁ A₁ ★ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ C₂ A₂ ★ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ (C₁ ⇒ C₂) (A₁ ⇒ A₂) ★ Δᴸ Δᴿ

  paired-star-arrow :
    ∀ {Δᴸ Δᴿ C₁ C₂ B₁ B₂} →
    PairedLower Σ Δᶜ C₁ ★ B₁ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ C₂ ★ B₂ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ (C₁ ⇒ C₂) ★ (B₁ ⇒ B₂) Δᴸ Δᴿ

  paired-arrow-stars :
    ∀ {Δᴸ Δᴿ C₁ C₂} →
    PairedLower Σ Δᶜ C₁ ★ ★ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ C₂ ★ ★ Δᴸ Δᴿ →
    PairedLower Σ Δᶜ (C₁ ⇒ C₂) ★ ★ Δᴸ Δᴿ

  paired-var-var :
    ∀ {Δᴸ Δᴿ Z X Y} →
    Z ↦⟨ varᵛ X , varᵛ Y ⟩∈ Σ →
    Z < Δᶜ →
    X < Δᴸ →
    Y < Δᴿ →
    PairedLower Σ Δᶜ (＇ Z) (＇ X) (＇ Y) Δᴸ Δᴿ

  paired-var-star :
    ∀ {Δᴸ Δᴿ Z X} →
    Z ↦⟨ varᵛ X , ★ᵛ ⟩∈ Σ →
    Z < Δᶜ →
    X < Δᴸ →
    PairedLower Σ Δᶜ (＇ Z) (＇ X) ★ Δᴸ Δᴿ

  paired-star-var :
    ∀ {Δᴸ Δᴿ Z Y} →
    Z ↦⟨ ★ᵛ , varᵛ Y ⟩∈ Σ →
    Z < Δᶜ →
    Y < Δᴿ →
    PairedLower Σ Δᶜ (＇ Z) ★ (＇ Y) Δᴸ Δᴿ

  paired-var-stars :
    ∀ {Δᴸ Δᴿ Z} →
    Z ↦⟨ ★ᵛ , ★ᵛ ⟩∈ Σ →
    Z < Δᶜ →
    PairedLower Σ Δᶜ (＇ Z) ★ ★ Δᴸ Δᴿ

  paired-both :
    ∀ {Δᴸ Δᴿ C A B} →
    PairedLower (extend-span bothˢ Σ) (suc Δᶜ)
      C A B (suc Δᴸ) (suc Δᴿ) →
    PairedLower Σ Δᶜ (`∀ C) (`∀ A) (`∀ B) Δᴸ Δᴿ

  paired-left :
    ∀ {Δᴸ Δᴿ C A B} →
    occurs zero C ≡ true →
    PairedLower (extend-span leftˢ Σ) (suc Δᶜ)
      C A B (suc Δᴸ) Δᴿ →
    PairedLower Σ Δᶜ (`∀ C) (`∀ A) B Δᴸ Δᴿ

  paired-right :
    ∀ {Δᴸ Δᴿ C A B} →
    occurs zero C ≡ true →
    PairedLower (extend-span rightˢ Σ) (suc Δᶜ)
      C A B Δᴸ (suc Δᴿ) →
    PairedLower Σ Δᶜ (`∀ C) A (`∀ B) Δᴸ Δᴿ

  paired-neither :
    ∀ {Δᴸ Δᴿ C A B} →
    occurs zero C ≡ true →
    PairedLower (extend-span neitherˢ Σ) (suc Δᶜ)
      C A B Δᴸ Δᴿ →
    PairedLower Σ Δᶜ (`∀ C) A B Δᴸ Δᴿ

row-var-var-left :
  ∀ {Σ Z X Y} →
  Z ↦⟨ varᵛ X , varᵛ Y ⟩∈ Σ →
  (Z ˣ⊑ˣ X) ∈ left-context Σ
row-var-var-left (row-var-var Z⊑X Z⊑Y) = Z⊑X

row-var-var-right :
  ∀ {Σ Z X Y} →
  Z ↦⟨ varᵛ X , varᵛ Y ⟩∈ Σ →
  (Z ˣ⊑ˣ Y) ∈ right-context Σ
row-var-var-right (row-var-var Z⊑X Z⊑Y) = Z⊑Y

row-var-star-left :
  ∀ {Σ Z X} →
  Z ↦⟨ varᵛ X , ★ᵛ ⟩∈ Σ →
  (Z ˣ⊑ˣ X) ∈ left-context Σ
row-var-star-left (row-var-star Z⊑X Z⊑★) = Z⊑X

row-var-star-right :
  ∀ {Σ Z X} →
  Z ↦⟨ varᵛ X , ★ᵛ ⟩∈ Σ →
  (Z ˣ⊑★) ∈ right-context Σ
row-var-star-right (row-var-star Z⊑X Z⊑★) = Z⊑★

row-star-var-left :
  ∀ {Σ Z Y} →
  Z ↦⟨ ★ᵛ , varᵛ Y ⟩∈ Σ →
  (Z ˣ⊑★) ∈ left-context Σ
row-star-var-left (row-star-var Z⊑★ Z⊑Y) = Z⊑★

row-star-var-right :
  ∀ {Σ Z Y} →
  Z ↦⟨ ★ᵛ , varᵛ Y ⟩∈ Σ →
  (Z ˣ⊑ˣ Y) ∈ right-context Σ
row-star-var-right (row-star-var Z⊑★ Z⊑Y) = Z⊑Y

row-star-star-left :
  ∀ {Σ Z} →
  Z ↦⟨ ★ᵛ , ★ᵛ ⟩∈ Σ →
  (Z ˣ⊑★) ∈ left-context Σ
row-star-star-left (row-star-star Z⊑★ Z⊑★′) = Z⊑★

row-star-star-right :
  ∀ {Σ Z} →
  Z ↦⟨ ★ᵛ , ★ᵛ ⟩∈ Σ →
  (Z ˣ⊑★) ∈ right-context Σ
row-star-star-right (row-star-star Z⊑★ Z⊑★′) = Z⊑★′

paired-lower-left :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B} →
  PairedLower Σ Δᶜ C A B Δᴸ Δᴿ →
  left-context Σ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ
paired-lower-left paired-star = id★
paired-lower-left paired-base-base = idι
paired-lower-left paired-base-star = idι
paired-lower-left paired-star-base = tag _
paired-lower-left paired-base-stars = tag _
paired-lower-left (paired-arrow-arrow p q) =
  paired-lower-left p ↦ paired-lower-left q
paired-lower-left (paired-arrow-star p q) =
  paired-lower-left p ↦ paired-lower-left q
paired-lower-left (paired-star-arrow p q) =
  tag paired-lower-left p ⇛ paired-lower-left q
paired-lower-left (paired-arrow-stars p q) =
  tag paired-lower-left p ⇛ paired-lower-left q
paired-lower-left (paired-var-var row Z<Δ X<Δ Y<Δ) =
  idˣ (row-var-var-left row) Z<Δ X<Δ
paired-lower-left (paired-var-star row Z<Δ X<Δ) =
  idˣ (row-var-star-left row) Z<Δ X<Δ
paired-lower-left (paired-star-var row Z<Δ Y<Δ) =
  tagˣ (row-star-var-left row) Z<Δ
paired-lower-left (paired-var-stars row Z<Δ) =
  tagˣ (row-star-star-left row) Z<Δ
paired-lower-left (paired-both lower) =
  ∀ⁱ paired-lower-left lower
paired-lower-left (paired-left occ lower) =
  ∀ⁱ paired-lower-left lower
paired-lower-left (paired-right occ lower) =
  ν occ (paired-lower-left lower)
paired-lower-left (paired-neither occ lower) =
  ν occ (paired-lower-left lower)

paired-lower-right :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B} →
  PairedLower Σ Δᶜ C A B Δᴸ Δᴿ →
  right-context Σ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
paired-lower-right paired-star = id★
paired-lower-right paired-base-base = idι
paired-lower-right paired-base-star = tag _
paired-lower-right paired-star-base = idι
paired-lower-right paired-base-stars = tag _
paired-lower-right (paired-arrow-arrow p q) =
  paired-lower-right p ↦ paired-lower-right q
paired-lower-right (paired-arrow-star p q) =
  tag paired-lower-right p ⇛ paired-lower-right q
paired-lower-right (paired-star-arrow p q) =
  paired-lower-right p ↦ paired-lower-right q
paired-lower-right (paired-arrow-stars p q) =
  tag paired-lower-right p ⇛ paired-lower-right q
paired-lower-right (paired-var-var row Z<Δ X<Δ Y<Δ) =
  idˣ (row-var-var-right row) Z<Δ Y<Δ
paired-lower-right (paired-var-star row Z<Δ X<Δ) =
  tagˣ (row-var-star-right row) Z<Δ
paired-lower-right (paired-star-var row Z<Δ Y<Δ) =
  idˣ (row-star-var-right row) Z<Δ Y<Δ
paired-lower-right (paired-var-stars row Z<Δ) =
  tagˣ (row-star-star-right row) Z<Δ
paired-lower-right (paired-both lower) =
  ∀ⁱ paired-lower-right lower
paired-lower-right (paired-left occ lower) =
  ν occ (paired-lower-right lower)
paired-lower-right (paired-right occ lower) =
  ∀ⁱ paired-lower-right lower
paired-lower-right (paired-neither occ lower) =
  ν occ (paired-lower-right lower)

pair-lower :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B} →
  left-context Σ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  right-context Σ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  PairedLower Σ Δᶜ C A B Δᴸ Δᴿ
pair-lower id★ id★ = paired-star
pair-lower idι idι = paired-base-base
pair-lower idι (tag ι) = paired-base-star
pair-lower (tag ι) idι = paired-star-base
pair-lower (tag ι) (tag .ι) = paired-base-stars
pair-lower (p₁ ↦ p₂) (q₁ ↦ q₂) =
  paired-arrow-arrow (pair-lower p₁ q₁) (pair-lower p₂ q₂)
pair-lower (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  paired-arrow-star (pair-lower p₁ q₁) (pair-lower p₂ q₂)
pair-lower (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  paired-star-arrow (pair-lower p₁ q₁) (pair-lower p₂ q₂)
pair-lower (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  paired-arrow-stars (pair-lower p₁ q₁) (pair-lower p₂ q₂)
pair-lower (idˣ Z⊑X Z<Δ X<Δ) (idˣ Z⊑Y _ Y<Δ) =
  paired-var-var (row-var-var Z⊑X Z⊑Y) Z<Δ X<Δ Y<Δ
pair-lower (idˣ Z⊑X Z<Δ X<Δ) (tagˣ Z⊑★ _) =
  paired-var-star (row-var-star Z⊑X Z⊑★) Z<Δ X<Δ
pair-lower (tagˣ Z⊑★ Z<Δ) (idˣ Z⊑Y _ Y<Δ) =
  paired-star-var (row-star-var Z⊑★ Z⊑Y) Z<Δ Y<Δ
pair-lower (tagˣ Z⊑★ Z<Δ) (tagˣ Z⊑★′ _) =
  paired-var-stars (row-star-star Z⊑★ Z⊑★′) Z<Δ
pair-lower (∀ⁱ p) (∀ⁱ q) = paired-both (pair-lower p q)
pair-lower (∀ⁱ p) (ν occ q) = paired-left occ (pair-lower p q)
pair-lower (ν occ p) (∀ⁱ q) = paired-right occ (pair-lower p q)
pair-lower (ν occ p) (ν occ′ q) = paired-neither occ (pair-lower p q)

record SpanPullback (Φ : ImpCtx) (source target : SpanCtx) : Set where
  field
    pull-variable :
      ∀ {Z W L R} →
      Z ↦⟨ L , R ⟩∈ source →
      W ↦⟨ L , R ⟩∈ target →
      (Z ˣ⊑ˣ W) ∈ Φ

open SpanPullback

root-pullback :
  ∀ {Φ Δ} →
  SpanPullback Φ (span Φ Φ) (span (idᵢ Δ) (idᵢ Δ))
root-pullback .pull-variable
    (row-var-var z⊑x z⊑y) (row-var-var w⊑x w⊑y) =
  subst (λ K → (_ ˣ⊑ˣ K) ∈ _)
    (sym (idᵢ-var-identity w⊑x)) z⊑x
root-pullback .pull-variable
    (row-var-star z⊑x z⊑★) (row-var-star w⊑x w⊑★) =
  ⊥-elim (idᵢ-no-star w⊑★)
root-pullback .pull-variable
    (row-star-var z⊑★ z⊑y) (row-star-var w⊑★ w⊑y) =
  ⊥-elim (idᵢ-no-star w⊑★)
root-pullback .pull-variable
    (row-star-star z⊑★ z⊑★′) (row-star-star w⊑★ w⊑★′) =
  ⊥-elim (idᵢ-no-star w⊑★)

span-variable-factor :
  ∀ {Φ source target Δᶜ Δᵒ Z W L R} →
  SpanPullback Φ source target →
  Z ↦⟨ L , R ⟩∈ source →
  W ↦⟨ L , R ⟩∈ target →
  Z < Δᶜ →
  W < Δᵒ →
  Φ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ W ⊣ Δᵒ
span-variable-factor pull source-row target-row Z<Δᶜ W<Δᵒ =
  idˣ (pull-variable pull source-row target-row) Z<Δᶜ W<Δᵒ

paired-variable-factor :
  ∀ {Φ source target Δᶜ Δᴸ Δᴿ Δᵒ Z W A B} →
  SpanPullback Φ source target →
  PairedLower source Δᶜ (＇ Z) A B Δᴸ Δᴿ →
  PairedLower target Δᵒ (＇ W) A B Δᴸ Δᴿ →
  Φ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ W ⊣ Δᵒ
paired-variable-factor pull
    (paired-var-var source-row Z<Δᶜ X<Δᴸ Y<Δᴿ)
    (paired-var-var target-row W<Δᵒ X<Δᴸ′ Y<Δᴿ′) =
  span-variable-factor pull source-row target-row Z<Δᶜ W<Δᵒ
paired-variable-factor pull
    (paired-var-star source-row Z<Δᶜ X<Δᴸ)
    (paired-var-star target-row W<Δᵒ X<Δᴸ′) =
  span-variable-factor pull source-row target-row Z<Δᶜ W<Δᵒ
paired-variable-factor pull
    (paired-star-var source-row Z<Δᶜ Y<Δᴿ)
    (paired-star-var target-row W<Δᵒ Y<Δᴿ′) =
  span-variable-factor pull source-row target-row Z<Δᶜ W<Δᵒ
paired-variable-factor pull
    (paired-var-stars source-row Z<Δᶜ)
    (paired-var-stars target-row W<Δᵒ) =
  span-variable-factor pull source-row target-row Z<Δᶜ W<Δᵒ
