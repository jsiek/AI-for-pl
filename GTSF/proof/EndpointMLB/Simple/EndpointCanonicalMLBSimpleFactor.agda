module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactor where

-- File Charter:
--   * Establishes the variable leaves for cross-context factorization through
--     the raw endpoint MLB enumeration.
--   * Uses a target route to resolve non-functional source imprecision
--     contexts without assuming a unique image for each source variable.
--   * Supplies the leaf cases for the paired route-history induction.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (false; true)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym)

open import Types
open import Imprecision using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_; id★; idˣ; idι; _↦_; ∀ⁱ_; tag_; tag_⇛_
  ; tagˣ; ν
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  (∀ᵢᶜ; νᵢᶜ)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePermutation using
  ( Exposure; bothᵉ; leftᵉ; rightᵉ; apply-left; apply-right
  ; apply-common-depth; apply-left-depth; apply-right-depth
  ; LeftStarPath; path-left-∀; path-right-∀; path-arrow₁
  ; path-arrow₂; path-arrow-star₁; path-arrow-star₂; path-var-star
  ; no-left-star-path; occurs-var-true→≡
  ; occurs-var-refl; ∨-true-left; ∨-true-right
  ; LeftOrigin; left-origin-both; left-origin-left
  ; left-origin-under-both; left-origin-under-left
  ; left-origin-under-right
  ; RightOrigin; right-origin-both; right-origin-right
  ; right-origin-under-both; right-origin-under-left
  ; right-origin-under-right
  ; StarRightPath; star-path-left-∀; star-path-right-∀
  ; star-path-arrow₁; star-path-arrow₂; star-path-star-arrow₁
  ; star-path-star-arrow₂; star-path-star-var; no-right-star-path
  ; no-⇑ᴸ-zero-star; un⇑ᴸ-star; var-candidate-member-shape
  )
open import proof.Core.Properties.ImprecisionProperties using
  ( idᵢ-no-star; idᵢ-var-identity
  ; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left; un⇑ᵢ-★∈; un⇑ᵢ-ˣ∈; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈
  )


record VarTrack (Φ : ImpCtx) (X Y : TyVar) : Set where
  field
    track-var : ∀ {Z} → (X ˣ⊑ˣ Z) ∈ Φ → Z ≡ Y
    track-star : (X ˣ⊑★) ∈ Φ → ⊥

open VarTrack

record TargetTrack (Φ : ImpCtx) (Y X : TyVar) : Set where
  field
    track-source : ∀ {Z} → (Z ˣ⊑ˣ Y) ∈ Φ → Z ≡ X

open TargetTrack

target-track-∀-zero : ∀ {Φ} → TargetTrack (∀ᵢᶜ Φ) zero zero
target-track-∀-zero .track-source (here refl) = refl
target-track-∀-zero .track-source (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)

target-track-∀ :
  ∀ {Φ X Y} →
  TargetTrack Φ Y X →
  TargetTrack (∀ᵢᶜ Φ) (suc Y) (suc X)
target-track-∀ track .track-source {Z = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
target-track-∀ track .track-source {Z = suc z} (there x∈) =
  cong suc (track-source track (un⇑ᵢ-ˣ∈ x∈))

target-track-ν :
  ∀ {Φ X Y} →
  TargetTrack Φ Y X →
  TargetTrack (νᵢᶜ Φ) Y (suc X)
target-track-ν track .track-source {Z = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
target-track-ν track .track-source {Z = suc z} (there x∈) =
  cong suc (track-source track (un⇑ᴸᵢ-ˣ∈ x∈))

record StarTrack (Φ : ImpCtx) (X : TyVar) : Set where
  field
    track-no-var : ∀ {Y} → (X ˣ⊑ˣ Y) ∈ Φ → ⊥

open StarTrack

var-track-∀-zero : ∀ {Φ} → VarTrack (∀ᵢᶜ Φ) zero zero
var-track-∀-zero .track-var (here refl) = refl
var-track-∀-zero .track-var (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
var-track-∀-zero .track-star (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)

star-track-ν-zero : ∀ {Φ} → StarTrack (νᵢᶜ Φ) zero
star-track-ν-zero .track-no-var (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)

var-track-∀ :
  ∀ {Φ X Y} →
  VarTrack Φ X Y →
  VarTrack (∀ᵢᶜ Φ) (suc X) (suc Y)
var-track-∀ track .track-var {Z = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
var-track-∀ track .track-var {Z = suc z} (there x∈) =
  cong suc (track-var track (un⇑ᵢ-ˣ∈ x∈))
var-track-∀ track .track-star (there x∈) =
  track-star track (un⇑ᵢ-★∈ x∈)

var-track-ν :
  ∀ {Φ X Y} →
  VarTrack Φ X Y →
  VarTrack (νᵢᶜ Φ) (suc X) Y
var-track-ν track .track-var (there x∈) =
  track-var track (un⇑ᴸᵢ-ˣ∈ x∈)
var-track-ν track .track-star (there x∈) =
  track-star track (un⇑ᴸ-star x∈)

left-origin-var-track :
  ∀ {modes Φ X L} →
  LeftOrigin modes X bothᵉ L →
  VarTrack (apply-left modes Φ) X L
left-origin-var-track left-origin-both = var-track-∀-zero
left-origin-var-track (left-origin-under-both origin) =
  var-track-∀ (left-origin-var-track origin)
left-origin-var-track (left-origin-under-left origin) =
  var-track-∀ (left-origin-var-track origin)
left-origin-var-track (left-origin-under-right origin) =
  var-track-ν (left-origin-var-track origin)

left-origin-target-track :
  ∀ {modes Φ X L} →
  LeftOrigin modes X bothᵉ L →
  TargetTrack (apply-left modes Φ) L X
left-origin-target-track left-origin-both = target-track-∀-zero
left-origin-target-track (left-origin-under-both origin) =
  target-track-∀ (left-origin-target-track origin)
left-origin-target-track (left-origin-under-left origin) =
  target-track-∀ (left-origin-target-track origin)
left-origin-target-track (left-origin-under-right origin) =
  target-track-ν (left-origin-target-track origin)

right-origin-var-track :
  ∀ {modes Φ X R} →
  RightOrigin modes X bothᵉ R →
  VarTrack (apply-right modes Φ) X R
right-origin-var-track right-origin-both = var-track-∀-zero
right-origin-var-track (right-origin-under-both origin) =
  var-track-∀ (right-origin-var-track origin)
right-origin-var-track (right-origin-under-left origin) =
  var-track-ν (right-origin-var-track origin)
right-origin-var-track (right-origin-under-right origin) =
  var-track-∀ (right-origin-var-track origin)

right-origin-target-track :
  ∀ {modes Φ X R} →
  RightOrigin modes X bothᵉ R →
  TargetTrack (apply-right modes Φ) R X
right-origin-target-track right-origin-both = target-track-∀-zero
right-origin-target-track (right-origin-under-both origin) =
  target-track-∀ (right-origin-target-track origin)
right-origin-target-track (right-origin-under-left origin) =
  target-track-ν (right-origin-target-track origin)
right-origin-target-track (right-origin-under-right origin) =
  target-track-∀ (right-origin-target-track origin)

source-var-star-incompatible :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C X L R} →
  TargetTrack Φᴸ L X →
  VarTrack Φᴿ X R →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ ＇ L ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ C ⊑ ★ ⊣ Δᴿ →
  ⊥
source-var-star-incompatible left right
    (idˣ z⊑l Z<Δ L<Δ) (tagˣ z⊑★ Z<Δ′)
    with track-source left z⊑l
source-var-star-incompatible left right
    (idˣ z⊑l Z<Δ L<Δ) (tagˣ z⊑★ Z<Δ′) | refl =
  track-star right z⊑★
source-var-star-incompatible left right (ν _ occ p) (ν _ occ′ q) =
  source-var-star-incompatible
    (target-track-ν left) (var-track-ν right) p q

source-star-var-incompatible :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C X L R} →
  VarTrack Φᴸ X L →
  TargetTrack Φᴿ R X →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ C ⊑ ＇ R ⊣ Δᴿ →
  ⊥
source-star-var-incompatible left right
    (tagˣ z⊑★ Z<Δ) (idˣ z⊑r Z<Δ′ R<Δ)
    with track-source right z⊑r
source-star-var-incompatible left right
    (tagˣ z⊑★ Z<Δ) (idˣ z⊑r Z<Δ′ R<Δ) | refl =
  track-star left z⊑★
source-star-var-incompatible left right (ν _ occ p) (ν _ occ′ q) =
  source-star-var-incompatible
    (var-track-ν left) (target-track-ν right) p q

occurs-tracked-variable :
  ∀ {Φ Δᴸ Δᴿ A B X Y} →
  VarTrack Φ X Y →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  occurs X A ≡ true →
  occurs Y B ≡ true
occurs-tracked-variable track id★ ()
occurs-tracked-variable {Y = Y} track (idˣ x∈ X<Δ Y<Δ) occ
    with occurs-var-true→≡ occ
occurs-tracked-variable {Y = Y} track (idˣ x∈ X<Δ Y<Δ) occ
    | refl rewrite track-var track x∈ =
  occurs-var-refl Y
occurs-tracked-variable track idι ()
occurs-tracked-variable {A = A₁ ⇒ A₂} {X = X} track
    (p ↦ q) occ with occurs X A₁ in occ₁
occurs-tracked-variable track (p ↦ q) occ | true =
  ∨-true-left (occurs-tracked-variable track p occ₁)
occurs-tracked-variable track (p ↦ q) occ | false =
  ∨-true-right (occurs-tracked-variable track q occ)
occurs-tracked-variable track (∀ⁱ p) occ =
  occurs-tracked-variable (var-track-∀ track) p occ
occurs-tracked-variable track (tag ι) ()
occurs-tracked-variable {A = A₁ ⇒ A₂} {X = X} track
    (tag p ⇛ q) occ with occurs X A₁ in occ₁
occurs-tracked-variable track (tag p ⇛ q) occ | true =
  occurs-tracked-variable track p occ₁
occurs-tracked-variable track (tag p ⇛ q) occ | false =
  occurs-tracked-variable track q occ
occurs-tracked-variable track (tagˣ x∈ X<Δ) occ
    with occurs-var-true→≡ occ
occurs-tracked-variable track (tagˣ x∈ X<Δ) occ | refl =
  ⊥-elim (track-star track x∈)
occurs-tracked-variable track (ν _ occA p) occ =
  occurs-tracked-variable (var-track-ν track) p occ

occurs-zero-factor-∀ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  occurs zero A ≡ true →
  occurs zero B ≡ true
occurs-zero-factor-∀ =
  occurs-tracked-variable var-track-∀-zero

star-track-∀ :
  ∀ {Φ X} →
  StarTrack Φ X →
  StarTrack (∀ᵢᶜ Φ) (suc X)
star-track-∀ track .track-no-var {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
star-track-∀ track .track-no-var {Y = suc y} (there x∈) =
  track-no-var track (un⇑ᵢ-ˣ∈ x∈)

star-track-ν :
  ∀ {Φ X} →
  StarTrack Φ X →
  StarTrack (νᵢᶜ Φ) (suc X)
star-track-ν track .track-no-var (there x∈) =
  track-no-var track (un⇑ᴸᵢ-ˣ∈ x∈)

source-left-used-path :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B X L} →
  VarTrack Φᴸ X L →
  StarTrack Φᴿ X →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  occurs X C ≡ true →
  LeftStarPath A B L
source-left-used-path left right id★ id★ ()
source-left-used-path left right
    (idˣ z⊑y Z<Δᶜ Y<Δᴸ) (idˣ z⊑w _ W<Δᴿ) occ =
  ⊥-elim
    (track-no-var right
      (subst (λ K → (K ˣ⊑ˣ _) ∈ _)
        (sym (occurs-var-true→≡ occ)) z⊑w))
source-left-used-path left right
    (idˣ z⊑y Z<Δᶜ Y<Δᴸ) (tagˣ z⊑★ _) occ
    with occurs-var-true→≡ occ
source-left-used-path left right
    (idˣ z⊑y Z<Δᶜ Y<Δᴸ) (tagˣ z⊑★ _) occ | refl
    with track-var left z⊑y
source-left-used-path left right
    (idˣ z⊑y Z<Δᶜ Y<Δᴸ) (tagˣ z⊑★ _) occ | refl | refl =
  path-var-star
source-left-used-path left right (tagˣ z⊑★ Z<Δᶜ) q occ =
  ⊥-elim
    (track-star left
      (subst (λ K → (K ˣ⊑★) ∈ _)
        (sym (occurs-var-true→≡ occ)) z⊑★))
source-left-used-path left right idι idι ()
source-left-used-path left right idι (tag ι) ()
source-left-used-path left right (tag ι) idι ()
source-left-used-path left right (tag ι) (tag .ι) ()
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ
    with occurs X A₁ in occ₁
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ | true =
  path-arrow₁ (source-left-used-path left right p₁ q₁ occ₁)
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ | false =
  path-arrow₂ (source-left-used-path left right p₂ q₂ occ)
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X A₁ in occ₁
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ | true =
  path-arrow-star₁ (source-left-used-path left right p₁ q₁ occ₁)
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ | false =
  path-arrow-star₂ (source-left-used-path left right p₂ q₂ occ)
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ
    with occurs X A₁ in occ₁
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ | true =
  ⊥-elim
    (no-left-star-path
      (source-left-used-path left right p₁ q₁ occ₁))
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ | false =
  ⊥-elim
    (no-left-star-path
      (source-left-used-path left right p₂ q₂ occ))
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X A₁ in occ₁
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ | true =
  ⊥-elim
    (no-left-star-path
      (source-left-used-path left right p₁ q₁ occ₁))
source-left-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ | false =
  ⊥-elim
    (no-left-star-path
      (source-left-used-path left right p₂ q₂ occ))
source-left-used-path left right (∀ⁱ p) (∀ⁱ q) occ =
  path-right-∀
    (path-left-∀
      (source-left-used-path
        (var-track-∀ left) (star-track-∀ right) p q occ))
source-left-used-path left right (∀ⁱ p) (ν _ occB q) occ =
  path-left-∀
    (source-left-used-path
      (var-track-∀ left) (star-track-ν right) p q occ)
source-left-used-path left right (ν _ occA p) (∀ⁱ q) occ =
  path-right-∀
    (source-left-used-path
      (var-track-ν left) (star-track-∀ right) p q occ)
source-left-used-path left right (ν _ occA p) (ν _ occB q) occ =
  source-left-used-path
    (var-track-ν left) (star-track-ν right) p q occ

source-left-exposure-path :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B} →
  ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ suc Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  occurs zero C ≡ true →
  LeftStarPath A B zero
source-left-exposure-path =
  source-left-used-path var-track-∀-zero star-track-ν-zero

source-right-used-path :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B X R} →
  StarTrack Φᴸ X →
  VarTrack Φᴿ X R →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  occurs X C ≡ true →
  StarRightPath A B R
source-right-used-path left right id★ id★ ()
source-right-used-path left right
    (idˣ z⊑w Z<Δᶜ W<Δᴸ) (idˣ z⊑y _ Y<Δᴿ) occ =
  ⊥-elim
    (track-no-var left
      (subst (λ K → (K ˣ⊑ˣ _) ∈ _)
        (sym (occurs-var-true→≡ occ)) z⊑w))
source-right-used-path left right p@(tagˣ z⊑★ Z<Δᶜ)
    (idˣ z⊑y _ Y<Δᴿ) occ
    with occurs-var-true→≡ occ
source-right-used-path left right (tagˣ z⊑★ Z<Δᶜ)
    (idˣ z⊑y _ Y<Δᴿ) occ | refl
    with track-var right z⊑y
source-right-used-path left right (tagˣ z⊑★ Z<Δᶜ)
    (idˣ z⊑y _ Y<Δᴿ) occ | refl | refl =
  star-path-star-var
source-right-used-path left right p (tagˣ z⊑★ Z<Δᶜ) occ =
  ⊥-elim
    (track-star right
      (subst (λ K → (K ˣ⊑★) ∈ _)
        (sym (occurs-var-true→≡ occ)) z⊑★))
source-right-used-path left right idι idι ()
source-right-used-path left right idι (tag ι) ()
source-right-used-path left right (tag ι) idι ()
source-right-used-path left right (tag ι) (tag .ι) ()
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ
    with occurs X A₁ in occ₁
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ | true =
  star-path-arrow₁ (source-right-used-path left right p₁ q₁ occ₁)
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (q₁ ↦ q₂) occ | false =
  star-path-arrow₂ (source-right-used-path left right p₂ q₂ occ)
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ
    with occurs X A₁ in occ₁
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ | true =
  star-path-star-arrow₁
    (source-right-used-path left right p₁ q₁ occ₁)
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) occ | false =
  star-path-star-arrow₂
    (source-right-used-path left right p₂ q₂ occ)
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X A₁ in occ₁
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ | true =
  ⊥-elim
    (no-right-star-path
      (source-right-used-path left right p₁ q₁ occ₁))
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) occ | false =
  ⊥-elim
    (no-right-star-path
      (source-right-used-path left right p₂ q₂ occ))
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X A₁ in occ₁
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ | true =
  ⊥-elim
    (no-right-star-path
      (source-right-used-path left right p₁ q₁ occ₁))
source-right-used-path {C = A₁ ⇒ A₂} {X = X} left right
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ | false =
  ⊥-elim
    (no-right-star-path
      (source-right-used-path left right p₂ q₂ occ))
source-right-used-path left right (∀ⁱ p) (∀ⁱ q) occ =
  star-path-left-∀
    (star-path-right-∀
      (source-right-used-path
        (star-track-∀ left) (var-track-∀ right) p q occ))
source-right-used-path left right (∀ⁱ p) (ν _ occB q) occ =
  star-path-left-∀
    (source-right-used-path
      (star-track-∀ left) (var-track-ν right) p q occ)
source-right-used-path left right (ν _ occA p) (∀ⁱ q) occ =
  star-path-right-∀
    (source-right-used-path
      (star-track-ν left) (var-track-∀ right) p q occ)
source-right-used-path left right (ν _ occA p) (ν _ occB q) occ =
  source-right-used-path
    (star-track-ν left) (var-track-ν right) p q occ

source-right-exposure-path :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B} →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ suc Δᴿ →
  occurs zero C ≡ true →
  StarRightPath A B zero
source-right-exposure-path =
  source-right-used-path star-track-ν-zero var-track-∀-zero
