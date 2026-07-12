module proof.EndpointCanonicalMLBSimpleFactor where

-- File Charter:
--   * Establishes the variable leaves for cross-context factorization through
--     the raw endpoint MLB enumeration.
--   * Uses a target route to resolve non-functional source imprecision
--     contexts without assuming a unique image for each source variable.
--   * Supplies the leaf cases for the paired route-history induction.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym)

open import Types
open import Imprecision using
  (ImpCtx; idᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_; id★; idˣ; idι; _↦_; ∀ⁱ_; tag_; tag_⇛_
  ; tagˣ; ν
  )
open import proof.EndpointCanonicalMLBSimple using
  (hasStar; hasVar; varCandidate?; varCandidatesUpTo; ∀ᵢᶜ; νᵢᶜ)
open import proof.EndpointCanonicalMLBSimplePermutation using
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
open import proof.EndpointCanonicalMLBSimpleRoutes using
  (EnumRoute; route-vars; route-var-star; route-star-var)
open import proof.EndpointCanonicalMLBSimpleSoundness using
  (andᵇ-true; hasStar-sound; hasVar-sound; varCandidate?-sound)
open import proof.ImprecisionProperties using
  ( WfImpCtx-to²; idᵢ-no-star; idᵢ-var-identity; idᵢ-wf
  ; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left; un⇑ᵢ-★∈; un⇑ᵢ-ˣ∈; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈
  )

apply-output : List Exposure → ImpCtx → ImpCtx
apply-output [] Φ = Φ
apply-output (_ ∷ modes) Φ = ∀ᵢᶜ (apply-output modes Φ)

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
source-var-star-incompatible left right (ν occ p) (ν occ′ q) =
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
source-star-var-incompatible left right (ν occ p) (ν occ′ q) =
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
occurs-tracked-variable track (ν occA p) occ =
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
source-left-used-path left right (∀ⁱ p) (ν occB q) occ =
  path-left-∀
    (source-left-used-path
      (var-track-∀ left) (star-track-ν right) p q occ)
source-left-used-path left right (ν occA p) (∀ⁱ q) occ =
  path-right-∀
    (source-left-used-path
      (var-track-ν left) (star-track-∀ right) p q occ)
source-left-used-path left right (ν occA p) (ν occB q) occ =
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
source-right-used-path left right (∀ⁱ p) (ν occB q) occ =
  star-path-left-∀
    (source-right-used-path
      (star-track-∀ left) (var-track-ν right) p q occ)
source-right-used-path left right (ν occA p) (∀ⁱ q) occ =
  star-path-right-∀
    (source-right-used-path
      (star-track-ν left) (var-track-∀ right) p q occ)
source-right-used-path left right (ν occA p) (ν occB q) occ =
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

history-var-var-member :
  ∀ {modes Φ Δ X Y Z W} →
  (Z ˣ⊑ˣ X) ∈ apply-left modes Φ →
  (Z ˣ⊑ˣ Y) ∈ apply-right modes Φ →
  (W ˣ⊑ˣ X) ∈ apply-left modes (idᵢ Δ) →
  (W ˣ⊑ˣ Y) ∈ apply-right modes (idᵢ Δ) →
  (Z ˣ⊑ˣ W) ∈ apply-output modes Φ
history-var-var-member {modes = []} z⊑x z⊑y w⊑x w⊑y =
  subst (λ V → (_ ˣ⊑ˣ V) ∈ _) (sym (idᵢ-var-identity w⊑x)) z⊑x
history-var-var-member {modes = bothᵉ ∷ modes} {W = zero}
    z⊑x z⊑y (there w⊑x) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
history-var-var-member {modes = bothᵉ ∷ modes} {W = zero}
    z⊑x z⊑y (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
history-var-var-member {modes = bothᵉ ∷ modes} {W = zero}
    (there z⊑x) z⊑y (here refl) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑x)
history-var-var-member {modes = bothᵉ ∷ modes} {W = zero}
    (here refl) (there z⊑y) (here refl) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑y)
history-var-var-member {modes = bothᵉ ∷ modes} {W = zero}
    (here refl) (here refl) (here refl) (here refl) =
  here refl
history-var-var-member
    {modes = bothᵉ ∷ modes} {X = zero} {W = suc W}
    z⊑x z⊑y (there w⊑x) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
history-var-var-member
    {modes = bothᵉ ∷ modes} {X = suc X} {Y = zero} {W = suc W}
    z⊑x z⊑y (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
history-var-var-member
    {modes = bothᵉ ∷ modes} {X = suc X} {Y = suc Y}
    {Z = zero} {W = suc W}
    (there z⊑x) z⊑y (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑x)
history-var-var-member
    {modes = bothᵉ ∷ modes} {X = suc X} {Y = suc Y}
    {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑y) (there w⊑x) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-var-member
        {modes = modes} {X = X} {Y = Y} {Z = z} {W = W}
        (un⇑ᵢ-ˣ∈ z⊑x) (un⇑ᵢ-ˣ∈ z⊑y)
        (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y)))
history-var-var-member {modes = leftᵉ ∷ modes} {W = zero}
    z⊑x z⊑y w⊑x (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
history-var-var-member
    {modes = leftᵉ ∷ modes} {X = zero} {W = suc W}
    z⊑x z⊑y (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
history-var-var-member
    {modes = leftᵉ ∷ modes} {X = suc X}
    {Z = zero} {W = suc W}
    (there z⊑x) z⊑y (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑x)
history-var-var-member
    {modes = leftᵉ ∷ modes} {X = suc X}
    {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑y) (there w⊑x) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-var-member
        {modes = modes} {X = X} {Z = z} {W = W}
        (un⇑ᵢ-ˣ∈ z⊑x) (un⇑ᴸᵢ-ˣ∈ z⊑y)
        (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y)))
history-var-var-member {modes = rightᵉ ∷ modes} {W = zero}
    z⊑x z⊑y (there w⊑x) w⊑y =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
history-var-var-member
    {modes = rightᵉ ∷ modes} {Y = zero} {W = suc W}
    z⊑x z⊑y (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
history-var-var-member
    {modes = rightᵉ ∷ modes} {Y = suc Y}
    {Z = zero} {W = suc W}
    z⊑x (there z⊑y) (there w⊑x) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑y)
history-var-var-member
    {modes = rightᵉ ∷ modes} {Y = suc Y}
    {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑y) (there w⊑x) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-var-member
        {modes = modes} {Y = Y} {Z = z} {W = W}
        (un⇑ᴸᵢ-ˣ∈ z⊑x) (un⇑ᵢ-ˣ∈ z⊑y)
        (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y)))

history-var-star-member :
  ∀ {modes Φ Δ X Z W} →
  (Z ˣ⊑ˣ X) ∈ apply-left modes Φ →
  (Z ˣ⊑★) ∈ apply-right modes Φ →
  (W ˣ⊑ˣ X) ∈ apply-left modes (idᵢ Δ) →
  (W ˣ⊑★) ∈ apply-right modes (idᵢ Δ) →
  (Z ˣ⊑ˣ W) ∈ apply-output modes Φ
history-var-star-member {modes = []} z⊑x z⊑★ w⊑x w⊑★ =
  ⊥-elim (idᵢ-no-star w⊑★)
history-var-star-member {modes = bothᵉ ∷ modes} {W = zero}
    z⊑x z⊑★ w⊑x (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
history-var-star-member
    {modes = bothᵉ ∷ modes} {X = zero} {W = suc W}
    z⊑x z⊑★ (there w⊑x) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
history-var-star-member
    {modes = bothᵉ ∷ modes} {X = suc X}
    {Z = zero} {W = suc W}
    (there z⊑x) z⊑★ (there w⊑x) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑x)
history-var-star-member
    {modes = bothᵉ ∷ modes} {X = suc X}
    {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑★) (there w⊑x) (there w⊑★) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-star-member
        {modes = modes} {X = X} {Z = z} {W = W}
        (un⇑ᵢ-ˣ∈ z⊑x) (un⇑ᵢ-★∈ z⊑★)
        (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★)))
history-var-star-member {modes = leftᵉ ∷ modes} {W = zero}
    z⊑x z⊑★ (there w⊑x) w⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
history-var-star-member {modes = leftᵉ ∷ modes} {W = zero}
    z⊑x z⊑★ (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᴸ-zero-star w⊑★)
history-var-star-member {modes = leftᵉ ∷ modes} {W = zero}
    (there z⊑x) z⊑★ (here refl) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑x)
history-var-star-member {modes = leftᵉ ∷ modes} {W = zero}
    (here refl) (there z⊑★) (here refl) (here refl) =
  ⊥-elim (no-⇑ᴸ-zero-star z⊑★)
history-var-star-member {modes = leftᵉ ∷ modes} {W = zero}
    (here refl) (here refl) (here refl) (here refl) =
  here refl
history-var-star-member
    {modes = leftᵉ ∷ modes} {X = zero} {W = suc W}
    z⊑x z⊑★ (there w⊑x) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
history-var-star-member
    {modes = leftᵉ ∷ modes} {X = suc X}
    {Z = zero} {W = suc W}
    (there z⊑x) z⊑★ (there w⊑x) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑x)
history-var-star-member
    {modes = leftᵉ ∷ modes} {X = suc X}
    {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑★) (there w⊑x) (there w⊑★) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-star-member
        {modes = modes} {X = X} {Z = z} {W = W}
        (un⇑ᵢ-ˣ∈ z⊑x) (un⇑ᴸ-star z⊑★)
        (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸ-star w⊑★)))
history-var-star-member {modes = rightᵉ ∷ modes} {W = zero}
    z⊑x z⊑★ (there w⊑x) w⊑★ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
history-var-star-member
    {modes = rightᵉ ∷ modes} {Z = zero} {W = suc W}
    (there z⊑x) z⊑★ (there w⊑x) (there w⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left z⊑x)
history-var-star-member
    {modes = rightᵉ ∷ modes} {Z = suc z} {W = suc W}
    (there z⊑x) (there z⊑★) (there w⊑x) (there w⊑★) =
  there
    (⇑ᵢ-ˣ∈
      (history-var-star-member
        {modes = modes} {Z = z} {W = W}
        (un⇑ᴸᵢ-ˣ∈ z⊑x) (un⇑ᵢ-★∈ z⊑★)
        (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★)))

history-star-var-member :
  ∀ {modes Φ Δ Y Z W} →
  (Z ˣ⊑★) ∈ apply-left modes Φ →
  (Z ˣ⊑ˣ Y) ∈ apply-right modes Φ →
  (W ˣ⊑★) ∈ apply-left modes (idᵢ Δ) →
  (W ˣ⊑ˣ Y) ∈ apply-right modes (idᵢ Δ) →
  (Z ˣ⊑ˣ W) ∈ apply-output modes Φ
history-star-var-member {modes = []} z⊑★ z⊑y w⊑★ w⊑y =
  ⊥-elim (idᵢ-no-star w⊑★)
history-star-var-member {modes = bothᵉ ∷ modes} {W = zero}
    z⊑★ z⊑y (there w⊑★) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
history-star-var-member
    {modes = bothᵉ ∷ modes} {Y = zero} {W = suc W}
    z⊑★ z⊑y (there w⊑★) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
history-star-var-member
    {modes = bothᵉ ∷ modes} {Y = suc Y}
    {Z = zero} {W = suc W}
    z⊑★ (there z⊑y) (there w⊑★) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑y)
history-star-var-member
    {modes = bothᵉ ∷ modes} {Y = suc Y}
    {Z = suc z} {W = suc W}
    (there z⊑★) (there z⊑y) (there w⊑★) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-star-var-member
        {modes = modes} {Y = Y} {Z = z} {W = W}
        (un⇑ᵢ-★∈ z⊑★) (un⇑ᵢ-ˣ∈ z⊑y)
        (un⇑ᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y)))
history-star-var-member {modes = leftᵉ ∷ modes} {W = zero}
    z⊑★ z⊑y (there w⊑★) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
history-star-var-member
    {modes = leftᵉ ∷ modes} {Z = zero} {W = suc W}
    z⊑★ (there z⊑y) (there w⊑★) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left z⊑y)
history-star-var-member
    {modes = leftᵉ ∷ modes} {Z = suc z} {W = suc W}
    (there z⊑★) (there z⊑y) (there w⊑★) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-star-var-member
        {modes = modes} {Z = z} {W = W}
        (un⇑ᵢ-★∈ z⊑★) (un⇑ᴸᵢ-ˣ∈ z⊑y)
        (un⇑ᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y)))
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    z⊑★ z⊑y (there w⊑★) w⊑y =
  ⊥-elim (no-⇑ᴸ-zero-star w⊑★)
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    z⊑★ z⊑y (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    (there z⊑★) (there z⊑y) (here refl) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑y)
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    (there z⊑★) (here refl) (here refl) (here refl) =
  ⊥-elim (no-⇑ᴸ-zero-star z⊑★)
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    (here refl) (there z⊑y) (here refl) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑y)
history-star-var-member {modes = rightᵉ ∷ modes} {W = zero}
    (here refl) (here refl) (here refl) (here refl) =
  here refl
history-star-var-member
    {modes = rightᵉ ∷ modes} {Y = zero} {W = suc W}
    z⊑★ z⊑y (there w⊑★) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
history-star-var-member
    {modes = rightᵉ ∷ modes} {Y = suc Y}
    {Z = zero} {W = suc W}
    z⊑★ (there z⊑y) (there w⊑★) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑y)
history-star-var-member
    {modes = rightᵉ ∷ modes} {Y = suc Y}
    {Z = suc z} {W = suc W}
    (there z⊑★) (there z⊑y) (there w⊑★) (there w⊑y) =
  there
    (⇑ᵢ-ˣ∈
      (history-star-var-member
        {modes = modes} {Y = Y} {Z = z} {W = W}
        (un⇑ᴸ-star z⊑★) (un⇑ᵢ-ˣ∈ z⊑y)
        (un⇑ᴸ-star w⊑★) (un⇑ᵢ-ˣ∈ w⊑y)))

factor-vars-history :
  ∀ {modes fuel Φ Δᴸ Δᴿ X Y Z W} →
  apply-left modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ＇ X ⊣ apply-left-depth modes Δᴿ →
  apply-right modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ＇ Y ⊣ apply-right-depth modes Δᴿ →
  EnumRoute fuel
    (apply-left modes (idᵢ Δᴿ)) (apply-right modes (idᵢ Δᴿ))
    (apply-common-depth modes Δᴿ)
    (apply-left-depth modes Δᴿ) (apply-right-depth modes Δᴿ)
    (＇ X) (＇ Y) W →
  apply-output modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ W ⊣ apply-common-depth modes Δᴿ
factor-vars-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X} {Y = Y} {W = W}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (idˣ z⊑y _ Y<Δᴿ) (route-vars W∈)
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δᴿ}
      {Φᴸ = apply-left modes (idᵢ Δᴿ)}
      {Φᴿ = apply-right modes (idᵢ Δᴿ)}
      {A = ＇ X} {B = ＇ Y} {C = W} W∈
factor-vars-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X} {Y = Y}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (idˣ z⊑y _ Y<Δᴿ) (route-vars W∈)
    | V , refl , V<Δᴿ , ok
    with andᵇ-true
      {a = hasVar V X (apply-left modes (idᵢ Δᴿ))}
      {b = hasVar V Y (apply-right modes (idᵢ Δᴿ))} ok
factor-vars-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X} {Y = Y}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (idˣ z⊑y _ Y<Δᴿ) (route-vars W∈)
    | V , refl , V<Δᴿ , ok | v⊑x? , v⊑y? =
  idˣ
    (history-var-var-member
      {modes = modes} {Φ = _} {Δ = Δᴿ} {X = X} {Y = Y} {W = V}
      z⊑x z⊑y
      (hasVar-sound v⊑x?) (hasVar-sound v⊑y?))
    Z<Δᴸ V<Δᴿ

factor-var-star-history :
  ∀ {modes fuel Φ Δᴸ Δᴿ X Z W} →
  apply-left modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ＇ X ⊣ apply-left-depth modes Δᴿ →
  apply-right modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ★ ⊣ apply-right-depth modes Δᴿ →
  EnumRoute fuel
    (apply-left modes (idᵢ Δᴿ)) (apply-right modes (idᵢ Δᴿ))
    (apply-common-depth modes Δᴿ)
    (apply-left-depth modes Δᴿ) (apply-right-depth modes Δᴿ)
    (＇ X) ★ W →
  apply-output modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ W ⊣ apply-common-depth modes Δᴿ
factor-var-star-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X} {W = W}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (tagˣ z⊑★ _)
    (route-var-star W∈)
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δᴿ}
      {Φᴸ = apply-left modes (idᵢ Δᴿ)}
      {Φᴿ = apply-right modes (idᵢ Δᴿ)}
      {A = ＇ X} {B = ★} {C = W} W∈
factor-var-star-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (tagˣ z⊑★ _) (route-var-star W∈)
    | V , refl , V<Δᴿ , ok
    with andᵇ-true
      {a = hasVar V X (apply-left modes (idᵢ Δᴿ))}
      {b = hasStar V (apply-right modes (idᵢ Δᴿ))} ok
factor-var-star-history
    {modes = modes} {Δᴿ = Δᴿ} {X = X}
    (idˣ z⊑x Z<Δᴸ X<Δᴿ) (tagˣ z⊑★ _) (route-var-star W∈)
    | V , refl , V<Δᴿ , ok | v⊑x? , v⊑★? =
  idˣ
    (history-var-star-member
      {modes = modes} {Φ = _} {Δ = Δᴿ} {X = X} {W = V}
      z⊑x z⊑★
      (hasVar-sound v⊑x?) (hasStar-sound v⊑★?))
    Z<Δᴸ V<Δᴿ

factor-star-var-history :
  ∀ {modes fuel Φ Δᴸ Δᴿ Y Z W} →
  apply-left modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ★ ⊣ apply-left-depth modes Δᴿ →
  apply-right modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ ＇ Y ⊣ apply-right-depth modes Δᴿ →
  EnumRoute fuel
    (apply-left modes (idᵢ Δᴿ)) (apply-right modes (idᵢ Δᴿ))
    (apply-common-depth modes Δᴿ)
    (apply-left-depth modes Δᴿ) (apply-right-depth modes Δᴿ)
    ★ (＇ Y) W →
  apply-output modes Φ ∣ apply-common-depth modes Δᴸ
    ⊢ ＇ Z ⊑ W ⊣ apply-common-depth modes Δᴿ
factor-star-var-history
    {modes = modes} {Δᴿ = Δᴿ} {Y = Y} {W = W}
    (tagˣ z⊑★ Z<Δᴸ) (idˣ z⊑y _ Y<Δᴿ)
    (route-star-var W∈)
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δᴿ}
      {Φᴸ = apply-left modes (idᵢ Δᴿ)}
      {Φᴿ = apply-right modes (idᵢ Δᴿ)}
      {A = ★} {B = ＇ Y} {C = W} W∈
factor-star-var-history
    {modes = modes} {Δᴿ = Δᴿ} {Y = Y}
    (tagˣ z⊑★ Z<Δᴸ) (idˣ z⊑y _ Y<Δᴿ) (route-star-var W∈)
    | V , refl , V<Δᴿ , ok
    with andᵇ-true
      {a = hasStar V (apply-left modes (idᵢ Δᴿ))}
      {b = hasVar V Y (apply-right modes (idᵢ Δᴿ))} ok
factor-star-var-history
    {modes = modes} {Δᴿ = Δᴿ} {Y = Y}
    (tagˣ z⊑★ Z<Δᴸ) (idˣ z⊑y _ Y<Δᴿ) (route-star-var W∈)
    | V , refl , V<Δᴿ , ok | v⊑★? , v⊑y? =
  idˣ
    (history-star-var-member
      {modes = modes} {Φ = _} {Δ = Δᴿ} {Y = Y} {W = V}
      z⊑★ z⊑y
      (hasStar-sound v⊑★?) (hasVar-sound v⊑y?))
    Z<Δᴸ V<Δᴿ
