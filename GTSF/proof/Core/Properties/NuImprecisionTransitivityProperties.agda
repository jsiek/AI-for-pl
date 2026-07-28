module proof.Core.Properties.NuImprecisionTransitivityProperties where

-- File Charter:
--   * Generic indexed type-imprecision transitivity support.
--   * Tracks composition of imprecision contexts across `∀` and source-only
--     `ν` binders, including occurrence and non-variable side conditions.
--   * Contains no endpoint-MLB algorithm, cast typing, term relation, or
--     simulation result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Relation.Nullary using (no; yes)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using
  ( idᵢ-var-identity
  ; idᵢ-no-star
  ; ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; un⇑ᴸᵢ-ˣ∈
  ; no-⇑ᴸᵢ-zero-left
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties

νᵣᵢ : Renameᵗ → Renameᵗ
νᵣᵢ ρ X = suc (ρ X)

record ComposeCtxᵢ
    (ρ : Renameᵗ) (Δᴸ : TyCtx)
    (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    compose-map-varᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      X ≡ ρ Y

    compose-var-varᵢ :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑ˣ Z) ∈ Φᴿ →
      (X ˣ⊑ˣ Z) ∈ Φᴼ

    compose-var-starᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑★) ∈ Φᴿ →
      (X ˣ⊑★) ∈ Φᴼ

    compose-star-leftᵢ :
      ∀ {X} →
      X < Δᴸ →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴼ

open ComposeCtxᵢ

compose-idᵢ :
  ∀ Δ →
  ComposeCtxᵢ (λ X → X) Δ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
compose-idᵢ Δ .compose-map-varᵢ x∈ = idᵢ-var-identity x∈
compose-idᵢ Δ .compose-var-varᵢ x∈ y∈ =
  subst
    (λ Z → (_ ˣ⊑ˣ Z) ∈ idᵢ Δ)
    (idᵢ-var-identity y∈)
    x∈
compose-idᵢ Δ .compose-var-starᵢ x∈ y★∈ =
  ⊥-elim (idᵢ-no-star y★∈)
compose-idᵢ Δ .compose-star-leftᵢ X<Δ x★∈ =
  ⊥-elim (idᵢ-no-star x★∈)

compose-id-leftᵢ :
  ∀ Δ Φ →
  ComposeCtxᵢ (λ X → X) Δ (idᵢ Δ) Φ Φ
compose-id-leftᵢ Δ Φ .compose-map-varᵢ x∈ = idᵢ-var-identity x∈
compose-id-leftᵢ Δ Φ .compose-var-varᵢ x∈ y∈ =
  subst
    (λ X → (X ˣ⊑ˣ _) ∈ Φ)
    (sym (idᵢ-var-identity x∈))
    y∈
compose-id-leftᵢ Δ Φ .compose-var-starᵢ x∈ y★∈ =
  subst
    (λ X → (X ˣ⊑★) ∈ Φ)
    (sym (idᵢ-var-identity x∈))
    y★∈
compose-id-leftᵢ Δ Φ .compose-star-leftᵢ X<Δ x★∈ =
  ⊥-elim (idᵢ-no-star x★∈)

compose-∀∀ᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (extᵗ ρ) (suc Δᴸ)
    (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (here refl) =
  refl
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = suc Y}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = suc X} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀∀ᵢ comp .compose-var-varᵢ (here refl) (here refl) =
  here refl
compose-∀∀ᵢ comp .compose-var-varᵢ (here refl) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left y∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = zero} {Y = suc Y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = suc X} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ
    {X = suc X} {Y = suc Y} {Z = zero}
    (there x∈) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right y∈)
compose-∀∀ᵢ comp .compose-var-varᵢ
    {X = suc X} {Y = suc Y} {Z = suc z}
    (there x∈) (there y∈) =
  there (⇑ᵢ-ˣ∈
    (compose-var-varᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-ˣ∈ y∈)))
compose-∀∀ᵢ comp .compose-var-starᵢ (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star y★∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = zero} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = zero} {Y = suc Y}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = suc X} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y★∈) =
  there (⇑ᵢ-★∈
    (compose-var-starᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-★∈ y★∈)))
compose-∀∀ᵢ comp .compose-star-leftᵢ {X = zero} z<s
    (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀∀ᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there
    (⇑ᵢ-★∈ (compose-star-leftᵢ comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-∀νᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (extᵗ ρ) (suc Δᴸ)
    (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (νᵢᶜ Φᴼ)
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (here refl) =
  refl
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = suc Y}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = suc X} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀νᵢ comp .compose-var-varᵢ (here refl) (there y∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left y∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = zero} {Y = suc Y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = suc X} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y∈) =
  there (⇑ᴸᵢ-ˣ∈
    (compose-var-varᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-ˣ∈ y∈)))
compose-∀νᵢ comp .compose-var-starᵢ (here refl) (here refl) =
  here refl
compose-∀νᵢ comp .compose-var-starᵢ (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star y★∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = zero} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = zero} {Y = suc Y}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = suc X} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y★∈) =
  there (⇑ᴸᵢ-★∈
    (compose-var-starᵢ comp
      (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-★∈ y★∈)))
compose-∀νᵢ comp .compose-star-leftᵢ {X = zero} z<s
    (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀νᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there
    (⇑ᴸᵢ-★∈
      (compose-star-leftᵢ comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-νidᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (νᵣᵢ ρ) (suc Δᴸ)
    (νᵢᶜ Φᴸ) Φᴿ (νᵢᶜ Φᴼ)
compose-νidᵢ comp .compose-map-varᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-map-varᵢ {X = suc X} (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈))
compose-νidᵢ comp .compose-var-varᵢ {X = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-var-varᵢ {X = suc X} (there x∈) y∈ =
  there
    (⇑ᴸᵢ-ˣ∈ (compose-var-varᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈) y∈))
compose-νidᵢ comp .compose-var-starᵢ {X = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-var-starᵢ {X = suc X} (there x∈) y★∈ =
  there
    (⇑ᴸᵢ-★∈
      (compose-var-starᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈) y★∈))
compose-νidᵢ comp .compose-star-leftᵢ {X = zero} z<s (here refl) =
  here refl
compose-νidᵢ comp .compose-star-leftᵢ {X = zero} z<s (there x★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x★∈)
compose-νidᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there
    (⇑ᴸᵢ-★∈
      (compose-star-leftᵢ comp X<Δ (un⇑ᴸᵢ-★∈ x★∈)))

occurs-var-backᵢ :
  ∀ (ρ : Renameᵗ) (x : TyVar) {y z} →
  y ≡ ρ z →
  occurs x (＇ z) ≡ true →
  occurs (ρ x) (＇ y) ≡ true
occurs-var-backᵢ ρ x {y} {z} y≡ρz occ with x ≟ z
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl
    rewrite y≡ρx with ρ x ≟ ρ x
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl | yes refl = refl
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl | no ρx≢ρx =
  ⊥-elim (ρx≢ρx refl)
occurs-var-backᵢ ρ x {y} {z} y≡ρz () | no x≢z

occurs-backᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ Δᴹ A B} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  (X : TyVar) →
  Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
  occurs X B ≡ true →
  occurs (ρ X) A ≡ true
occurs-backᵢ comp X id★ ()
occurs-backᵢ comp X (idˣ x∈ _ _) occ =
  occurs-var-backᵢ _ X (compose-map-varᵢ comp x∈) occ
occurs-backᵢ comp X idι ()
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ
    with occurs X B₁ in occ₁
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | true =
  ∨-true-leftᵢ (occurs-backᵢ comp X p occ₁)
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false
    with occurs X B₂ in occ₂
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false | true =
  ∨-true-rightᵢ (occurs-backᵢ comp X q occ₂)
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false | false =
  ⊥-elim (false≠trueᵢ occ)
occurs-backᵢ comp X (∀ⁱ p) occ =
  occurs-backᵢ (compose-∀∀ᵢ comp) (suc X) p occ
occurs-backᵢ comp X (tag ι) ()
occurs-backᵢ comp X (tag_⇛_ p q) ()
occurs-backᵢ comp X (tagˣ x∈ _) ()
occurs-backᵢ comp X (ν nonvar occA p) occ =
  occurs-backᵢ (compose-νidᵢ comp) X p occ

nonVar-occurs-backᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  NonVar B →
  occurs zero B ≡ true →
  NonVar A
nonVar-occurs-backᵢ id★ nonvar-star ()
nonVar-occurs-backᵢ (idˣ x∈ X<Δ Y<Δ) () occ
nonVar-occurs-backᵢ idι nonvar-base ()
nonVar-occurs-backᵢ (p ↦ q) nonvar-fun occ = nonvar-fun
nonVar-occurs-backᵢ (∀ⁱ p) nonvar-all occ = nonvar-all
nonVar-occurs-backᵢ (tag ι) nonvar-star ()
nonVar-occurs-backᵢ (tag p ⇛ q) nonvar-star ()
nonVar-occurs-backᵢ (tagˣ x∈ X<Δ) nonvar-star ()
nonVar-occurs-backᵢ (ν nonvar occ p) safe occB = nonvar-all

nonVar-forward-if-occursᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  NonVar A →
  occurs zero B ≡ true →
  NonVar B
nonVar-forward-if-occursᵢ id★ nonvar-star ()
nonVar-forward-if-occursᵢ (idˣ x∈ X<Δ Y<Δ) () occ
nonVar-forward-if-occursᵢ idι nonvar-base ()
nonVar-forward-if-occursᵢ (p ↦ q) nonvar-fun occ = nonvar-fun
nonVar-forward-if-occursᵢ (∀ⁱ p) nonvar-all occ = nonvar-all
nonVar-forward-if-occursᵢ (tag ι) nonvar-base ()
nonVar-forward-if-occursᵢ (tag p ⇛ q) nonvar-fun ()
nonVar-forward-if-occursᵢ (tagˣ x∈ X<Δ) () occ
nonVar-forward-if-occursᵢ
    (ν inner occA p) nonvar-all occB =
  nonVar-forward-if-occursᵢ p inner occB

⊑-trans-composeᵢ :
  ∀ {ρ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
  Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ →
  Φᴼ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-composeᵢ comp id★ id★ = id★
⊑-trans-composeᵢ comp (idˣ x∈ X<Δ _) (idˣ y∈ _ Z<Δ) =
  idˣ (compose-var-varᵢ comp x∈ y∈) X<Δ Z<Δ
⊑-trans-composeᵢ comp (idˣ x∈ X<Δ _) (tagˣ y★∈ _) =
  tagˣ (compose-var-starᵢ comp x∈ y★∈) X<Δ
⊑-trans-composeᵢ comp idι idι = idι
⊑-trans-composeᵢ comp idι (tag ι) = tag ι
⊑-trans-composeᵢ comp (p₁ ↦ p₂) (q₁ ↦ q₂) =
  ⊑-trans-composeᵢ comp p₁ q₁ ↦ ⊑-trans-composeᵢ comp p₂ q₂
⊑-trans-composeᵢ comp (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  tag_⇛_
    (⊑-trans-composeᵢ comp p₁ q₁)
    (⊑-trans-composeᵢ comp p₂ q₂)
⊑-trans-composeᵢ comp (∀ⁱ p) (∀ⁱ q) =
  ∀ⁱ (⊑-trans-composeᵢ (compose-∀∀ᵢ comp) p q)
⊑-trans-composeᵢ comp (∀ⁱ p) (ν safe occ q) =
  ν (nonVar-occurs-backᵢ p safe occ)
    (occurs-backᵢ (compose-∀∀ᵢ comp) zero p occ)
    (⊑-trans-composeᵢ (compose-∀νᵢ comp) p q)
⊑-trans-composeᵢ comp (tag ι) id★ = tag ι
⊑-trans-composeᵢ comp (tag p ⇛ q) id★ =
  tag_⇛_
    (⊑-trans-composeᵢ comp p id★)
    (⊑-trans-composeᵢ comp q id★)
⊑-trans-composeᵢ comp (tagˣ x★∈ X<Δ) id★ =
  tagˣ (compose-star-leftᵢ comp X<Δ x★∈) X<Δ
⊑-trans-composeᵢ comp (ν safe occ p) q =
  ν safe occ (⊑-trans-composeᵢ (compose-νidᵢ comp) p q)

⊑-trans-idᵢ :
  ∀ {Δ A B C} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ B ⊑ C ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ A ⊑ C ⊣ Δ
⊑-trans-idᵢ {Δ = Δ} p q =
  ⊑-trans-composeᵢ (compose-idᵢ Δ) p q

⊑-trans-left-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  idᵢ Δᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴸ →
  Φ ∣ Δᴸ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-left-idᵢ {Φ = Φ} {Δᴸ = Δᴸ} p q =
  ⊑-trans-composeᵢ (compose-id-leftᵢ Δᴸ Φ) p q
