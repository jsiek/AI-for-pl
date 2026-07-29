module proof.ImprecisionComposition where

-- File Charter:
--   * Composes coercion-indexed GTPLC narrowings and widenings.
--   * Produces the result coercion together with its typing derivation.
--   * Uses endpoint equality to collapse identity-shaped tag/project
--     sequences.
--   * Depends on `NarrowWiden` and its context-indexed judgments.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z≤n; s≤s; _<_)
open import Data.Product using (_,_; ∃-syntax; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; subst; sym)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
  using (Coercion; renameᶜ)
  renaming
    ( id to idᶜ
    ; _↦_ to _↦ᶜ_
    ; `∀ to ∀ᶜ
    ; _! to _!ᶜ
    )
open import NarrowWiden
open import proof.TypeInTypeSubst using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; renameᵗ-preserves-WfTy
  ; rename-ext-preserves-zero∈
  )

------------------------------------------------------------------------
-- Identity imprecision contexts
------------------------------------------------------------------------

un⇑ᵢ-var : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᵢ-var {Φ = []} ()
un⇑ᵢ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-var X∈)
un⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-var X∈)

un⇑ᵢ-star : ∀ {Φ X}
  → (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
  → (X ˣ⊑★) ∈ Φ
un⇑ᵢ-star {Φ = []} ()
un⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-star X∈)
un⇑ᵢ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-star X∈)

⇑ᵢ-var : ∀ {Φ X Y}
  → (X ˣ⊑ˣ Y) ∈ Φ
  → (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
⇑ᵢ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᵢ-var X∈)
⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᵢ-var X∈)

⇑ᵢ-star : ∀ {Φ X}
  → (X ˣ⊑★) ∈ Φ
  → (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᵢ-star X∈)
⇑ᵢ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᵢ-star X∈)

no-⇑ᵢ-zero-left : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-left {Φ = []} ()
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-left X∈
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-left X∈

no-⇑ᵢ-zero-right : ∀ {Φ X}
  → (X ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-right {Φ = []} ()
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-right X∈
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-right X∈

no-⇑ᵢ-zero-star : ∀ {Φ}
  → (zero ˣ⊑★) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-star {Φ = []} ()
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-star X∈
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-star X∈

idᵢ-var-identity : ∀ {Δ X Y}
  → (X ˣ⊑ˣ Y) ∈ idᵢ Δ
  → X ≡ Y
idᵢ-var-identity {Δ = zero} ()
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero}
    (here refl) =
  refl
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = suc Y}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (idᵢ-var-identity (un⇑ᵢ-var X∈))

idᵢ-no-star : ∀ {Δ X}
  → (X ˣ⊑★) ∈ idᵢ Δ
  → ⊥
idᵢ-no-star {Δ = zero} ()
idᵢ-no-star {Δ = suc Δ} {X = zero} (there X∈) =
  no-⇑ᵢ-zero-star X∈
idᵢ-no-star {Δ = suc Δ} {X = suc X} (there X∈) =
  idᵢ-no-star (un⇑ᵢ-star X∈)

------------------------------------------------------------------------
-- Context composition
------------------------------------------------------------------------

record ComposeCtx
    (Δ : TyCtx) (Φᴵ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    compose-map-var : ∀ {X Y}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → X ≡ Y

    compose-var-var : ∀ {X Y Z}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → (Y ˣ⊑ˣ Z) ∈ Φᴿ
      → (X ˣ⊑ˣ Z) ∈ Φᴼ

    compose-var-star : ∀ {X Y}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → (Y ˣ⊑★) ∈ Φᴿ
      → (X ˣ⊑★) ∈ Φᴼ

    compose-star-left : ∀ {X}
      → X < Δ
      → (X ˣ⊑★) ∈ Φᴵ
      → (X ˣ⊑★) ∈ Φᴼ

open ComposeCtx

compose-id-left : ∀ Δ Φ
  → ComposeCtx Δ (idᵢ Δ) Φ Φ
compose-id-left Δ Φ .compose-map-var X∈ =
  idᵢ-var-identity X∈
compose-id-left Δ Φ .compose-var-var X∈ Y∈ =
  subst (λ X → (X ˣ⊑ˣ _) ∈ Φ)
    (sym (idᵢ-var-identity X∈)) Y∈
compose-id-left Δ Φ .compose-var-star X∈ Y∈ =
  subst (λ X → (X ˣ⊑★) ∈ Φ)
    (sym (idᵢ-var-identity X∈)) Y∈
compose-id-left Δ Φ .compose-star-left X<Δ X∈ =
  ⊥-elim (idᵢ-no-star X∈)

compose-all : ∀ {Δ Φᴵ Φᴿ Φᴼ}
  → ComposeCtx Δ Φᴵ Φᴿ Φᴼ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
compose-all comp .compose-map-var (here refl) = refl
compose-all comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-all comp .compose-var-var (here refl) (here refl) =
  here refl
compose-all comp .compose-var-var (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left Y∈)
compose-all comp .compose-var-var {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-var-var
    {X = suc X} {Y = suc Y} {Z = zero}
    (there X∈) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right Y∈)
compose-all comp .compose-var-var
    {X = suc X} {Y = suc Y} {Z = suc z}
    (there X∈) (there Y∈) =
  there (⇑ᵢ-var
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᵢ-var Y∈)))
compose-all comp .compose-var-star (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-star Y∈)
compose-all comp .compose-var-star {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᵢ-star
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᵢ-star Y∈)))
compose-all comp .compose-star-left {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-all comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᵢ-star
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

⇑ᴸ-var : ∀ {Φ X Y}
  → (X ˣ⊑ˣ Y) ∈ Φ
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-var X∈)
⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-var X∈)

un⇑ᴸ-var : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸ-var {Φ = []} ()
un⇑ᴸ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-var X∈)
un⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-var X∈)

no-⇑ᴸ-zero-left : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-left {Φ = []} ()
no-⇑ᴸ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-left X∈
no-⇑ᴸ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-left X∈

⇑ᴸ-star : ∀ {Φ X}
  → (X ˣ⊑★) ∈ Φ
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-star X∈)
⇑ᴸ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-star X∈)

un⇑ᴸ-star : ∀ {Φ X}
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑★) ∈ Φ
un⇑ᴸ-star {Φ = []} ()
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-star X∈)
un⇑ᴸ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-star X∈)

no-⇑ᴸ-zero-star : ∀ {Φ}
  → (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-star {Φ = []} ()
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-star X∈
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-star X∈

compose-all-gen : ∀ {Δ Φᴵ Φ}
  → ComposeCtx Δ Φᴵ Φ Φ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
compose-all-gen comp .compose-map-var (here refl) = refl
compose-all-gen comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-all-gen comp .compose-var-var (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᴸ-zero-left Y∈)
compose-all-gen comp .compose-var-var {X = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-var-var {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-var
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-var Y∈)))
compose-all-gen comp .compose-var-star (here refl) (here refl) =
  here refl
compose-all-gen comp .compose-var-star (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᴸ-zero-star Y∈)
compose-all-gen comp .compose-var-star {X = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-star
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-star Y∈)))
compose-all-gen comp .compose-star-left {X = zero}
    X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-all-gen comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-star
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

compose-gen : ∀ {Δ Φᴵ Φᴿ Φᴼ}
  → ComposeCtx Δ Φᴵ Φᴿ Φᴼ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑★) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴼ)
compose-gen comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-gen comp .compose-var-var {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-var-var {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-var
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-var Y∈)))
compose-gen comp .compose-var-star {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-star
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-star Y∈)))
compose-gen comp .compose-star-left {X = zero}
    (s≤s z≤n) (here refl) =
  here refl
compose-gen comp .compose-star-left {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-gen comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-star
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

------------------------------------------------------------------------
-- Asymmetric renaming
------------------------------------------------------------------------

rename-star-injective : ∀ {ρ A}
  → renameᵗ ρ A ≡ ★
  → A ≡ ★
rename-star-injective {A = ★} refl = refl

⇒-left-injective : ∀ {A B C D}
  → (A ⇒ B) ≡ (C ⇒ D)
  → A ≡ C
⇒-left-injective refl = refl

⇒-right-injective : ∀ {A B C D}
  → (A ⇒ B) ≡ (C ⇒ D)
  → B ≡ D
⇒-right-injective refl = refl

rename-fun-star-injective : ∀ {ρ A}
  → renameᵗ ρ A ≡ (★ ⇒ ★)
  → A ≡ (★ ⇒ ★)
rename-fun-star-injective {A = A ⇒ B} eq
    rewrite rename-star-injective (⇒-left-injective eq)
          | rename-star-injective (⇒-right-injective eq) =
  refl

rename-star-neq : ∀ {ρ A}
  → A ≢ ★
  → renameᵗ ρ A ≢ ★
rename-star-neq A≢★ eq = A≢★ (rename-star-injective eq)

rename-fun-star-neq : ∀ {ρ A}
  → A ≢ (★ ⇒ ★)
  → renameᵗ ρ A ≢ (★ ⇒ ★)
rename-fun-star-neq A≢★⇒★ eq =
  A≢★⇒★ (rename-fun-star-injective eq)

rename-fun-star-neqʳ : ∀ {ρ A}
  → (★ ⇒ ★) ≢ A
  → (★ ⇒ ★) ≢ renameᵗ ρ A
rename-fun-star-neqʳ ★⇒★≢A eq =
  ★⇒★≢A (sym (rename-fun-star-injective (sym eq)))

renameFirst : Renameᵗ → ImpAssm → ImpAssm
renameFirst ρ (X ˣ⊑★) = ρ X ˣ⊑★
renameFirst ρ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ Y

renameFirst-⇑ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ ⇑ᵢ Φ
  → renameFirst (extᵗ ρ) a ∈ ⇑ᵢ Ψ
renameFirst-⇑ {Φ = []} h ()
renameFirst-⇑ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (ρ X ˣ⊑★) ∈ Ψ
    → (suc (ρ X) ˣ⊑★) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (ρ X ˣ⊑ˣ Y) ∈ Ψ
    → (suc (ρ X) ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ {Φ = (_ ˣ⊑★) ∷ Φ} h (there a∈) =
  renameFirst-⇑ (λ b∈ → h (there b∈)) a∈
renameFirst-⇑ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (there a∈) =
  renameFirst-⇑ (λ b∈ → h (there b∈)) a∈

renameFirst-all : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ
  → renameFirst (extᵗ ρ) a
      ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ
renameFirst-all h (here refl) = here refl
renameFirst-all h (there a∈) = there (renameFirst-⇑ h a∈)

renameFirst-⇑ᴸ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ ⇑ᴸᵢ Φ
  → renameFirst (extᵗ ρ) a ∈ ⇑ᴸᵢ Ψ
renameFirst-⇑ᴸ {Φ = []} h ()
renameFirst-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (ρ X ˣ⊑★) ∈ Ψ
    → (suc (ρ X) ˣ⊑★) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (ρ X ˣ⊑ˣ Y) ∈ Ψ
    → (suc (ρ X) ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ᴸ {Φ = (_ ˣ⊑★) ∷ Φ} h (there a∈) =
  renameFirst-⇑ᴸ (λ b∈ → h (there b∈)) a∈
renameFirst-⇑ᴸ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (there a∈) =
  renameFirst-⇑ᴸ (λ b∈ → h (there b∈)) a∈

renameFirst-gen : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
  → renameFirst (extᵗ ρ) a
      ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ
renameFirst-gen h (here refl) = here refl
renameFirst-gen h (there a∈) = there (renameFirst-⇑ᴸ h a∈)

rename-first-⊑ᵃ : ∀ {ρ Φ Ψ A B}
  → (∀ {a} → a ∈ Φ → renameFirst ρ a ∈ Ψ)
  → (a : Atom A)
  → (b : Atom B)
  → Φ ⊢ a ⊑ᵃ b
  → Ψ ⊢ renameᵃ ρ a ⊑ᵃ b
rename-first-⊑ᵃ h (＇ X) (＇ Y) X∈ = h X∈
rename-first-⊑ᵃ h (＇ X) (‵ ι) ()
rename-first-⊑ᵃ h (＇ X) ★ ()
rename-first-⊑ᵃ h (‵ ι) (＇ Y) ()
rename-first-⊑ᵃ h (‵ ι) (‵ κ) refl = refl
rename-first-⊑ᵃ h (‵ ι) ★ ()
rename-first-⊑ᵃ h ★ (＇ Y) ()
rename-first-⊑ᵃ h ★ (‵ ι) ()
rename-first-⊑ᵃ h ★ ★ tt = tt

mutual

  rename-sourceʷ : ∀ {ρ Φ Ψ Δᴸ Δᴸ′ Δᴿ c A B}
    → (∀ {a} → a ∈ Φ → renameFirst ρ a ∈ Ψ)
    → TyRenameWf Δᴸ Δᴸ′ ρ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ′ ⊢ renameᶜ ρ c ⦂ renameᵗ ρ A ⊑ B ⊣ Δᴿ
  rename-sourceʷ {ρ = ρ} h hρ (idᵃ a b hA hB a⊑b) =
    idᵃ (renameᵃ ρ a) b
      (renameᵗ-preserves-WfTy hA hρ) hB
      (rename-first-⊑ᵃ h a b a⊑b)
  rename-sourceʷ h hρ (p ↦ q) =
    rename-targetⁿ h hρ p ↦ rename-sourceʷ h hρ q
  rename-sourceʷ h hρ (∀ʷ p) =
    ∀ʷ (rename-sourceʷ (renameFirst-all h)
      (TyRenameWf-ext hρ) p)
  rename-sourceʷ h hρ (tag ι) = tag ι
  rename-sourceʷ h hρ tag★⇒★ = tag★⇒★
  rename-sourceʷ h hρ (p ︔tag★⇒★[ A≢★⇒★ ]) =
    rename-sourceʷ h hρ p ︔tag★⇒★[
      rename-fun-star-neq A≢★⇒★ ]
  rename-sourceʷ h hρ (unseal X∈ X<Δᴸ) =
    unseal (h X∈) (hρ X<Δᴸ)
  rename-sourceʷ {ρ = ρ} h hρ (inst nonvar occ p B≢★) =
    inst (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (rename-sourceʷ (renameFirst-gen h)
        (TyRenameWf-ext hρ) p)
      B≢★

  rename-targetⁿ : ∀ {ρ Φ Ψ Δᴸ Δᴿ Δᴿ′ c A B}
    → (∀ {a} → a ∈ Φ → renameFirst ρ a ∈ Ψ)
    → TyRenameWf Δᴿ Δᴿ′ ρ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ renameᶜ ρ c ⦂ A ⊒ renameᵗ ρ B ⊣ Δᴿ′
  rename-targetⁿ {ρ = ρ} h hρ (idᵃ a b hA hB a⊒b) =
    idᵃ a (renameᵃ ρ b) hA
      (renameᵗ-preserves-WfTy hB hρ)
      (rename-first-⊑ᵃ h b a a⊒b)
  rename-targetⁿ h hρ (p ↦ q) =
    rename-sourceʷ h hρ p ↦ rename-targetⁿ h hρ q
  rename-targetⁿ h hρ (∀ⁿ p) =
    ∀ⁿ (rename-targetⁿ (renameFirst-all h)
      (TyRenameWf-ext hρ) p)
  rename-targetⁿ h hρ (untag ι) = untag ι
  rename-targetⁿ h hρ untag★⇒★ = untag★⇒★
  rename-targetⁿ h hρ (untag★⇒★︔ p [ ★⇒★≢B ]) =
    untag★⇒★︔ rename-targetⁿ h hρ p [
      rename-fun-star-neqʳ ★⇒★≢B ]
  rename-targetⁿ h hρ (seal X∈ X<Δᴿ) =
    seal (h X∈) (hρ X<Δᴿ)
  rename-targetⁿ {ρ = ρ} h hρ (gen nonvar occ p B≢★) =
    gen (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (rename-targetⁿ (renameFirst-gen h)
        (TyRenameWf-ext hρ) p)
      B≢★

renameFirst-suc-gen : ∀ {Φ a}
  → a ∈ Φ
  → renameFirst suc a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
renameFirst-suc-gen {a = X ˣ⊑★} X∈ =
  there (go X∈)
  where
  go : ∀ {Φ X}
    → (X ˣ⊑★) ∈ Φ
    → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  go {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  go {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) = there (go X∈)
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) = there (go X∈)
renameFirst-suc-gen {a = X ˣ⊑ˣ Y} X∈ =
  there (go X∈)
  where
  go : ∀ {Φ X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  go {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) = there (go X∈)
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) = there (go X∈)

source-liftʷ : ∀ {Φ Δᴸ Δᴿ c A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ renameᶜ suc c ⦂ ⇑ᵗ A ⊑ B ⊣ Δᴿ
source-liftʷ =
  rename-sourceʷ renameFirst-suc-gen (λ X<Δ → s≤s X<Δ)

target-liftⁿ : ∀ {Φ Δᴸ Δᴿ c A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ Δᴸ ⊢ renameᶜ suc c ⦂ A ⊒ ⇑ᵗ B ⊣ suc Δᴿ
target-liftⁿ =
  rename-targetⁿ renameFirst-suc-gen (λ X<Δ → s≤s X<Δ)

renameSecond : Renameᵗ → ImpAssm → ImpAssm
renameSecond ρ (X ˣ⊑★) = X ˣ⊑★
renameSecond ρ (X ˣ⊑ˣ Y) = X ˣ⊑ˣ ρ Y

renameSecond-⇑ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ⇑ᵢ Φ
  → renameSecond (extᵗ ρ) a ∈ ⇑ᵢ Ψ
renameSecond-⇑ {Φ = []} h ()
renameSecond-⇑ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (X ˣ⊑ˣ ρ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ suc (ρ Y)) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ {Φ = _ ∷ Φ} h (there X∈) =
  renameSecond-⇑ (λ Y∈ → h (there Y∈)) X∈

renameSecond-all : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
  → renameSecond (extᵗ ρ) a
      ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
renameSecond-all h (here refl) = here refl
renameSecond-all h (there X∈) =
  there (renameSecond-⇑ h X∈)

renameSecond-⇑ᴸ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ⇑ᴸᵢ Φ
  → renameSecond ρ a ∈ ⇑ᴸᵢ Ψ
renameSecond-⇑ᴸ {Φ = []} h ()
renameSecond-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h
    (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h
    (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (X ˣ⊑ˣ ρ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ ρ Y) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ᴸ {Φ = _ ∷ Φ} h (there X∈) =
  renameSecond-⇑ᴸ (λ Y∈ → h (there Y∈)) X∈

renameSecond-gen : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
  → renameSecond ρ a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
renameSecond-gen h (here refl) = here refl
renameSecond-gen h (there X∈) =
  there (renameSecond-⇑ᴸ h X∈)

rename-second-⊑ᵃ : ∀ {ρ Φ Ψ A B}
  → (∀ {a} → a ∈ Φ → renameSecond ρ a ∈ Ψ)
  → (a : Atom A)
  → (b : Atom B)
  → Φ ⊢ a ⊑ᵃ b
  → Ψ ⊢ a ⊑ᵃ renameᵃ ρ b
rename-second-⊑ᵃ h (＇ X) (＇ Y) X∈ = h X∈
rename-second-⊑ᵃ h (＇ X) (‵ ι) ()
rename-second-⊑ᵃ h (＇ X) ★ ()
rename-second-⊑ᵃ h (‵ ι) (＇ Y) ()
rename-second-⊑ᵃ h (‵ ι) (‵ κ) refl = refl
rename-second-⊑ᵃ h (‵ ι) ★ ()
rename-second-⊑ᵃ h ★ (＇ Y) ()
rename-second-⊑ᵃ h ★ (‵ ι) ()
rename-second-⊑ᵃ h ★ ★ tt = tt

mutual

  rename-targetʷ : ∀ {ρ Φ Ψ Δᴸ Δᴿ Δᴿ′ c A B}
    → (∀ {a} → a ∈ Φ → renameSecond ρ a ∈ Ψ)
    → TyRenameWf Δᴿ Δᴿ′ ρ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ c ⦂ A ⊑ renameᵗ ρ B ⊣ Δᴿ′
  rename-targetʷ {ρ = ρ} h hρ (idᵃ a b hA hB a⊑b) =
    idᵃ a (renameᵃ ρ b) hA
      (renameᵗ-preserves-WfTy hB hρ)
      (rename-second-⊑ᵃ h a b a⊑b)
  rename-targetʷ h hρ (p ↦ q) =
    rename-sourceⁿ h hρ p ↦ rename-targetʷ h hρ q
  rename-targetʷ h hρ (∀ʷ p) =
    ∀ʷ (rename-targetʷ (renameSecond-all h)
      (TyRenameWf-ext hρ) p)
  rename-targetʷ h hρ (tag ι) = tag ι
  rename-targetʷ h hρ tag★⇒★ = tag★⇒★
  rename-targetʷ h hρ (p ︔tag★⇒★[ A≢★⇒★ ]) =
    rename-targetʷ h hρ p ︔tag★⇒★[ A≢★⇒★ ]
  rename-targetʷ h hρ (unseal X∈ X<Δᴸ) =
    unseal (h X∈) X<Δᴸ
  rename-targetʷ h hρ (inst nonvar occ p B≢★) =
    inst nonvar occ
      (rename-targetʷ (renameSecond-gen h) hρ p)
      (rename-star-neq B≢★)

  rename-sourceⁿ : ∀ {ρ Φ Ψ Δᴸ Δᴸ′ Δᴿ c A B}
    → (∀ {a} → a ∈ Φ → renameSecond ρ a ∈ Ψ)
    → TyRenameWf Δᴸ Δᴸ′ ρ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ′ ⊢ c ⦂ renameᵗ ρ A ⊒ B ⊣ Δᴿ
  rename-sourceⁿ {ρ = ρ} h hρ (idᵃ a b hA hB a⊒b) =
    idᵃ (renameᵃ ρ a) b
      (renameᵗ-preserves-WfTy hA hρ) hB
      (rename-second-⊑ᵃ h b a a⊒b)
  rename-sourceⁿ h hρ (p ↦ q) =
    rename-targetʷ h hρ p ↦ rename-sourceⁿ h hρ q
  rename-sourceⁿ h hρ (∀ⁿ p) =
    ∀ⁿ (rename-sourceⁿ (renameSecond-all h)
      (TyRenameWf-ext hρ) p)
  rename-sourceⁿ h hρ (untag ι) = untag ι
  rename-sourceⁿ h hρ untag★⇒★ = untag★⇒★
  rename-sourceⁿ h hρ (untag★⇒★︔ p [ ★⇒★≢B ]) =
    untag★⇒★︔ rename-sourceⁿ h hρ p [ ★⇒★≢B ]
  rename-sourceⁿ h hρ (seal X∈ X<Δᴿ) =
    seal (h X∈) X<Δᴿ
  rename-sourceⁿ h hρ (gen nonvar occ p B≢★) =
    gen nonvar occ
      (rename-sourceⁿ (renameSecond-gen h) hρ p)
      (rename-star-neq B≢★)

renameSecond-suc : ∀ {Φ a}
  → a ∈ Φ
  → renameSecond suc a ∈ ⇑ᴿᵢ Φ
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑★}
    (here refl) =
  here refl
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑★}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑★}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (here refl) =
  here refl
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (there X∈) =
  there (renameSecond-suc X∈)

target-liftʷ : ∀ {Φ Δᴸ Δᴿ c A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
target-liftʷ =
  rename-targetʷ renameSecond-suc (λ X<Δ → s≤s X<Δ)

source-liftⁿ : ∀ {Φ Δᴸ Δᴿ c A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → ⇑ᴿᵢ Φ ∣ suc Δᴸ ⊢ c ⦂ ⇑ᵗ A ⊒ B ⊣ Δᴿ
source-liftⁿ =
  rename-sourceⁿ renameSecond-suc (λ X<Δ → s≤s X<Δ)

⇑ᴿ-⇑ᴸ : ∀ Φ
  → ⇑ᴿᵢ (⇑ᴸᵢ Φ) ≡ ⇑ᵢ Φ
⇑ᴿ-⇑ᴸ [] = refl
⇑ᴿ-⇑ᴸ ((X ˣ⊑★) ∷ Φ) =
  cong ((suc X ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ)
⇑ᴿ-⇑ᴸ ((X ˣ⊑ˣ Y) ∷ Φ) =
  cong ((suc X ˣ⊑ˣ suc Y) ∷_) (⇑ᴿ-⇑ᴸ Φ)

source-lift-genⁿ : ∀ {Φ Δᴸ Δᴿ c A B}
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ suc Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ c ⦂ ⇑ᵗ A ⊒ B ⊣ suc Δᴿ
source-lift-genⁿ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {c = c} {A = A} {B = B} p =
  subst
    (λ Ψ → Ψ ∣ suc Δᴸ ⊢ c ⦂ ⇑ᵗ A ⊒ B ⊣ suc Δᴿ)
    (cong ((zero ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ))
    (source-liftⁿ p)

target-lift-genʷ : ∀ {Φ Δᴸ Δᴿ c A B}
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ c ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
target-lift-genʷ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {c = c} {A = A} {B = B} p =
  subst
    (λ Ψ → Ψ ∣ suc Δᴸ ⊢ c ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ)
    (cong ((zero ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ))
    (target-liftʷ p)

------------------------------------------------------------------------
-- Recontexting relations whose exposed endpoint is ground
------------------------------------------------------------------------

StarIncl : TyCtx → ImpCtx → ImpCtx → Set
StarIncl Δ Φ Ψ =
  ∀ {X} → X < Δ → (X ˣ⊑★) ∈ Φ → (X ˣ⊑★) ∈ Ψ

gen-star-incl : ∀ {Δ Φ Ψ}
  → StarIncl Δ Φ Ψ
  → StarIncl (suc Δ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
gen-star-incl incl (s≤s z≤n) (here refl) = here refl
gen-star-incl incl {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᴸ-zero-star X∈)
gen-star-incl incl {X = suc X} (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-star (incl X<Δ (un⇑ᴸ-star X∈)))

mutual

  recontext-to-starʷ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c A}
    → StarIncl Δᴸ Ψ Φ
    → Ψ ∣ Δᴸ ⊢ c ⦂ A ⊑ ★ ⊣ Δᴹ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ ★ ⊣ Δᴿ
  recontext-to-starʷ incl (idᵃ ★ ★ hA hB tt) =
    idᵃ ★ ★ hA wf★ tt
  recontext-to-starʷ incl (tag ι) = tag ι
  recontext-to-starʷ incl tag★⇒★ = tag★⇒★
  recontext-to-starʷ incl (p ︔tag★⇒★[ A≢★⇒★ ]) =
    recontext-to-funʷ incl p ︔tag★⇒★[ A≢★⇒★ ]
  recontext-to-starʷ incl (unseal X∈ X<Δ) =
    unseal (incl X<Δ X∈) X<Δ
  recontext-to-starʷ incl (inst nonvar occ p ★≢★) =
    ⊥-elim (★≢★ refl)

  recontext-to-funʷ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c A}
    → StarIncl Δᴸ Ψ Φ
    → Ψ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴹ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
  recontext-to-funʷ incl (p ↦ q) =
    recontext-from-starⁿ incl p ↦ recontext-to-starʷ incl q
  recontext-to-funʷ incl (inst nonvar occ p ★⇒★≢★) =
    inst nonvar occ
      (recontext-to-funʷ (gen-star-incl incl) p) ★⇒★≢★

  recontext-from-starⁿ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c B}
    → StarIncl Δᴿ Ψ Φ
    → Ψ ∣ Δᴹ ⊢ c ⦂ ★ ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ c ⦂ ★ ⊒ B ⊣ Δᴿ
  recontext-from-starⁿ incl (idᵃ ★ ★ hA hB tt) =
    idᵃ ★ ★ wf★ hB tt
  recontext-from-starⁿ incl (untag ι) = untag ι
  recontext-from-starⁿ incl untag★⇒★ = untag★⇒★
  recontext-from-starⁿ incl
      (untag★⇒★︔ p [ ★⇒★≢B ]) =
    untag★⇒★︔ recontext-from-funⁿ incl p [ ★⇒★≢B ]
  recontext-from-starⁿ incl (seal X∈ X<Δ) =
    seal (incl X<Δ X∈) X<Δ
  recontext-from-starⁿ incl (gen nonvar occ p ★≢★) =
    ⊥-elim (★≢★ refl)

  recontext-from-funⁿ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c B}
    → StarIncl Δᴿ Ψ Φ
    → Ψ ∣ Δᴹ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
  recontext-from-funⁿ incl (p ↦ q) =
    recontext-to-starʷ incl p ↦ recontext-from-starⁿ incl q
  recontext-from-funⁿ incl (gen nonvar occ p ★⇒★≢★) =
    gen nonvar occ
      (recontext-from-funⁿ (gen-star-incl incl) p) ★⇒★≢★

------------------------------------------------------------------------
-- Occurrence and non-variable transport
------------------------------------------------------------------------

VarMap : Renameᵗ → ImpCtx → Set
VarMap ρ Φ =
  ∀ {X Y} → (X ˣ⊑ˣ Y) ∈ Φ → X ≡ ρ Y

all-var-map : ∀ {ρ Φ}
  → VarMap ρ Φ
  → VarMap (extᵗ ρ) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
all-var-map h (here refl) = refl
all-var-map h {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
all-var-map h {X = suc X} {Y = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
all-var-map h {X = suc X} {Y = suc Y} (there X∈) =
  cong suc (h (un⇑ᵢ-var X∈))

νRename : Renameᵗ → Renameᵗ
νRename ρ X = suc (ρ X)

gen-var-map : ∀ {ρ Φ}
  → VarMap ρ Φ
  → VarMap (νRename ρ) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
gen-var-map h {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᴸ-zero-left X∈)
gen-var-map h {X = suc X} (there X∈) =
  cong suc (h (un⇑ᴸ-var X∈))

mutual

  member-backʷ : ∀ {ρ Φ Δᴸ Δᴿ c A B X}
    → VarMap ρ Φ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → X ∈ᵗ B
    → ρ X ∈ᵗ A
  member-backʷ h (idᵃ (＇ X) (＇ Y) hA hB X∈) var-∈
      rewrite h X∈ =
    var-∈
  member-backʷ h (idᵃ (‵ ι) (＇ Y) hA hB ()) var-∈
  member-backʷ h (idᵃ ★ (＇ Y) hA hB ()) var-∈
  member-backʷ h (idᵃ a (‵ ι) hA hB a⊑b) ()
  member-backʷ h (idᵃ a ★ hA hB a⊑b) ()
  member-backʷ h (p ↦ q) (∈-fun-left X∈) =
    ∈-fun-left (member-backⁿ h p X∈)
  member-backʷ h (p ↦ q) (∈-fun-right X∈) =
    ∈-fun-right (member-backʷ h q X∈)
  member-backʷ h (∀ʷ p) (∈-all X∈) =
    ∈-all (member-backʷ (all-var-map h) p X∈)
  member-backʷ h (tag ι) ()
  member-backʷ h tag★⇒★ ()
  member-backʷ h (_ ︔tag★⇒★[ _ ]) ()
  member-backʷ h (unseal X∈ X<Δ) ()
  member-backʷ h (inst nonvar occ p B≢★) X∈ =
    ∈-all (member-backʷ (gen-var-map h) p X∈)

  member-backⁿ : ∀ {ρ Φ Δᴸ Δᴿ c A B X}
    → VarMap ρ Φ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → X ∈ᵗ A
    → ρ X ∈ᵗ B
  member-backⁿ h (idᵃ (＇ X) (＇ Y) hA hB X∈) var-∈
      rewrite h X∈ =
    var-∈
  member-backⁿ h (idᵃ (＇ X) (‵ ι) hA hB ()) var-∈
  member-backⁿ h (idᵃ (＇ X) ★ hA hB ()) var-∈
  member-backⁿ h (idᵃ (‵ ι) b hA hB a⊒b) ()
  member-backⁿ h (idᵃ ★ b hA hB a⊒b) ()
  member-backⁿ h (p ↦ q) (∈-fun-left X∈) =
    ∈-fun-left (member-backʷ h p X∈)
  member-backⁿ h (p ↦ q) (∈-fun-right X∈) =
    ∈-fun-right (member-backⁿ h q X∈)
  member-backⁿ h (∀ⁿ p) (∈-all X∈) =
    ∈-all (member-backⁿ (all-var-map h) p X∈)
  member-backⁿ h (untag ι) ()
  member-backⁿ h untag★⇒★ ()
  member-backⁿ h (untag★⇒★︔ _ [ _ ]) ()
  member-backⁿ h (seal X∈ X<Δ) ()
  member-backⁿ h (gen nonvar occ p B≢★) X∈ =
    ∈-all (member-backⁿ (gen-var-map h) p X∈)

nonvar-backʷ : ∀ {Φ Δᴸ Δᴿ c A B X}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → NonVar B
  → X ∈ᵗ B
  → NonVar A
nonvar-backʷ (idᵃ a (＇ Y) hA hB a⊑b) ()
nonvar-backʷ (idᵃ a (‵ ι) hA hB a⊑b) nonvar-base ()
nonvar-backʷ (idᵃ a ★ hA hB a⊑b) nonvar-star ()
nonvar-backʷ (p ↦ q) nonvar-fun X∈ = nonvar-fun
nonvar-backʷ (∀ʷ p) nonvar-all X∈ = nonvar-all
nonvar-backʷ (tag ι) nonvar-star ()
nonvar-backʷ tag★⇒★ nonvar-star ()
nonvar-backʷ (_ ︔tag★⇒★[ _ ]) nonvar-star ()
nonvar-backʷ (unseal X∈ X<Δ) nonvar-star ()
nonvar-backʷ (inst nonvar occ p B≢★) nonvarB X∈ =
  nonvar-all

nonvar-backⁿ : ∀ {Φ Δᴸ Δᴿ c A B X}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → NonVar A
  → X ∈ᵗ A
  → NonVar B
nonvar-backⁿ (idᵃ (＇ X) b hA hB a⊒b) ()
nonvar-backⁿ (idᵃ (‵ ι) b hA hB a⊒b) nonvar-base ()
nonvar-backⁿ (idᵃ ★ b hA hB a⊒b) nonvar-star ()
nonvar-backⁿ (p ↦ q) nonvar-fun X∈ = nonvar-fun
nonvar-backⁿ (∀ⁿ p) nonvar-all X∈ = nonvar-all
nonvar-backⁿ (untag ι) nonvar-star ()
nonvar-backⁿ untag★⇒★ nonvar-star ()
nonvar-backⁿ (untag★⇒★︔ _ [ _ ]) nonvar-star ()
nonvar-backⁿ (seal X∈ X<Δ) nonvar-star ()
nonvar-backⁿ (gen nonvar occ p B≢★) nonvarA X∈ =
  nonvar-all

------------------------------------------------------------------------
-- Polymorphic boundary helpers
------------------------------------------------------------------------

fun-idʷ : ∀ {Φ Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ idᶜ ↦ᶜ idᶜ ⦂
      (★ ⇒ ★) ⊑ (★ ⇒ ★) ⊣ Δᴿ
fun-idʷ =
  idᵃ ★ ★ wf★ wf★ tt ↦ idᵃ ★ ★ wf★ wf★ tt

fun-idⁿ : ∀ {Φ Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ idᶜ ↦ᶜ idᶜ ⦂
      (★ ⇒ ★) ⊒ (★ ⇒ ★) ⊣ Δᴿ
fun-idⁿ =
  idᵃ ★ ★ wf★ wf★ tt ↦ idᵃ ★ ★ wf★ wf★ tt

strip-tag★⇒★ : ∀ {c Φ Δᴸ Δᴿ A}
  → NonVar A
  → zero ∈ᵗ A
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ ★ ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
strip-tag★⇒★ nonvar-star () p
strip-tag★⇒★ nonvar-base () p
strip-tag★⇒★ nonvar-fun occ tag★⇒★ = _ , fun-idʷ
strip-tag★⇒★ nonvar-fun occ (p ︔tag★⇒★[ _ ]) = _ , p
strip-tag★⇒★ nonvar-all occ (p ︔tag★⇒★[ _ ]) = _ , p
strip-tag★⇒★ nonvar-all occ (inst nonvar occ′ p ★≢★) =
  ⊥-elim (★≢★ refl)

strip-untag★⇒★ : ∀ {c Φ Δᴸ Δᴿ B}
  → NonVar B
  → zero ∈ᵗ B
  → Φ ∣ Δᴸ ⊢ c ⦂ ★ ⊒ B ⊣ Δᴿ
  → ∃[ d ] Φ ∣ Δᴸ ⊢ d ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
strip-untag★⇒★ nonvar-star () p
strip-untag★⇒★ nonvar-base () p
strip-untag★⇒★ nonvar-fun occ untag★⇒★ = _ , fun-idⁿ
strip-untag★⇒★ nonvar-fun occ (untag★⇒★︔ p [ _ ]) = _ , p
strip-untag★⇒★ nonvar-all occ (untag★⇒★︔ p [ _ ]) = _ , p
strip-untag★⇒★ nonvar-all occ (gen nonvar occ′ p ★≢★) =
  ⊥-elim (★≢★ refl)

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

mutual

  composeⁿ : ∀ {c d Φᴵ Φ Δᴸ Δᴿ A B C}
    → ComposeCtx Δᴿ Φᴵ Φ Φ
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → Φᴵ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ
    → ∃[ r ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ
  composeⁿ {c} comp p (idᵃ (＇ X) (＇ Y) hB hC Y⊑X)
      rewrite compose-map-var comp Y⊑X =
    c , p
  composeⁿ comp p (idᵃ (＇ X) (‵ ι) hB hC ())
  composeⁿ comp p (idᵃ (＇ X) ★ hB hC ())
  composeⁿ comp p (idᵃ (‵ ι) (＇ Y) hB hC ())
  composeⁿ {c} comp p (idᵃ (‵ ι) (‵ κ) hB hC refl) =
    c , p
    
  composeⁿ comp p (idᵃ (‵ ι) ★ hB hC ())
  composeⁿ comp p (idᵃ ★ (＇ Y) hB hC ())
  composeⁿ comp p (idᵃ ★ (‵ ι) hB hC ())
  composeⁿ {c} comp p (idᵃ ★ ★ hB hC tt) = c , p
  
  composeⁿ {c}{d} comp (idᵃ ★ ★ hA hB tt) q =
    d , recontext-from-starⁿ (compose-star-left comp) q
    
  composeⁿ comp untag★⇒★ q
      with wrap-untag★⇒★
        (recontext-from-funⁿ (compose-star-left comp) q)
  composeⁿ comp untag★⇒★ q | r , r⊢ = r , r⊢
  composeⁿ comp (untag★⇒★︔ p [ _ ]) q
      with composeⁿ comp p q
  composeⁿ comp (untag★⇒★︔ p [ _ ]) q | r , r⊢
      with wrap-untag★⇒★ r⊢
  composeⁿ comp (untag★⇒★︔ p [ _ ]) q | r , r⊢
      | s , s⊢ =
    s , s⊢
    
  composeⁿ comp (gen nonvarB occB p B≢★) (∀ⁿ q)
      with composeⁿ (compose-all-gen comp) p q
  composeⁿ comp (gen nonvarB occB p B≢★) (∀ⁿ q)
      | r , r⊢ =
    Coercions.gen r , gen nonvarC occC r⊢ B≢★
    where
    occC = member-backⁿ
      (all-var-map (compose-map-var comp)) q occB
    nonvarC = nonvar-backⁿ q nonvarB occB
    
  composeⁿ {A = A} comp p (gen nonvarC occC q B≢★)
      with composeⁿ (compose-gen comp) (target-liftⁿ p) (source-lift-genⁿ q)
  composeⁿ {A = A} comp p (gen nonvarC occC q B≢★)
      | r , r⊢
      with A ≟Ty ★
  composeⁿ {A = .★} comp p (gen nonvarC occC q B≢★)
      | r , r⊢ | yes refl
      with strip-untag★⇒★ nonvarC occC r⊢
  composeⁿ {A = .★} comp p (gen nonvarC occC q B≢★)
      | r , r⊢ | yes refl | s , s⊢
      with wrap-untag★⇒★ (gen nonvarC occC s⊢ (λ ()))
  composeⁿ {A = .★} comp p (gen nonvarC occC q B≢★)
      | r , r⊢ | yes refl | s , s⊢ | t , t⊢ =
    t , t⊢
  composeⁿ {A = A} comp p (gen nonvarC occC q B≢★)
      | r , r⊢ | no A≢★ =
    Coercions.gen r , gen nonvarC occC r⊢ A≢★
    
  composeⁿ comp (p₁ ↦ p₂) (q₁ ↦ q₂)
      with composeʷ comp q₁ p₁ | composeⁿ comp p₂ q₂
  composeⁿ comp (p₁ ↦ p₂) (q₁ ↦ q₂)
      | r₁ , r₁⊢ | r₂ , r₂⊢ =
    r₁ ↦ᶜ r₂ , (r₁⊢ ↦ r₂⊢)
    
  composeⁿ comp (∀ⁿ p) (∀ⁿ q)
      with composeⁿ (compose-all comp) p q
  composeⁿ comp (∀ⁿ p) (∀ⁿ q) | r , r⊢ =
    ∀ᶜ r , ∀ⁿ r⊢

  composeʷ : ∀ {c d Φᴵ Φ Δᴸ Δᴿ A B C}
    → ComposeCtx Δᴸ Φᴵ Φ Φ
    → Φᴵ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴸ
    → Φ ∣ Δᴸ ⊢ d ⦂ B ⊑ C ⊣ Δᴿ
    → ∃[ r ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ
  composeʷ {c} comp p (idᵃ ★ ★ hB hC tt) =
    c , recontext-to-starʷ (compose-star-left comp) p
  composeʷ comp
      (idᵃ (‵ ι) (‵ κ) hA hB refl)
      (idᵃ (‵ .κ) (‵ ν) hB′ hC refl) =
    idᶜ , idᵃ (‵ ι) (‵ ν) hA hC refl
  composeʷ comp (idᵃ (‵ ι) (‵ κ) hA hB refl) (tag .κ) =
    (‵ κ) !ᶜ , tag κ
  composeʷ comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊑Y)
      (idᵃ (＇ .Y) (＇ z) hB′ hC Y⊑Z) =
    idᶜ , idᵃ (＇ X) (＇ z) hA hC
      (compose-var-var comp X⊑Y Y⊑Z)
  composeʷ comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊑Y)
      (unseal Y∈ Y<Δ′)
      rewrite compose-map-var comp X⊑Y =
    Coercions.unseal Y , unseal Y∈ Y<Δ′
  composeʷ comp p tag★⇒★
      with wrap-tag★⇒★
        (recontext-to-funʷ (compose-star-left comp) p)
  composeʷ comp p tag★⇒★ | r , r⊢ = r , r⊢
  composeʷ comp p (q ︔tag★⇒★[ _ ])
      with composeʷ comp p q
  composeʷ comp p (q ︔tag★⇒★[ _ ]) | r , r⊢
      with wrap-tag★⇒★ r⊢
  composeʷ comp p (q ︔tag★⇒★[ _ ]) | r , r⊢
      | s , s⊢ =
    s , s⊢
  composeʷ comp (∀ʷ p) (inst nonvarB occB q C≢★)
      with composeʷ (compose-all-gen comp) p q
  composeʷ comp (∀ʷ p) (inst nonvarB occB q C≢★)
      | r , r⊢ =
    Coercions.inst r , inst nonvarA occA r⊢ C≢★
    where
    occA = member-backʷ
      (all-var-map (compose-map-var comp)) p occB
    nonvarA = nonvar-backʷ p nonvarB occB
  composeʷ {C = C} comp (inst nonvarA occA p B≢★) q
      with composeʷ (compose-gen comp)
        (target-lift-genʷ p) (source-liftʷ q)
  composeʷ {C = C} comp (inst nonvarA occA p B≢★) q
      | r , r⊢
      with C ≟Ty ★
  composeʷ {C = .★} comp (inst nonvarA occA p B≢★) q
      | r , r⊢ | yes refl
      with strip-tag★⇒★ nonvarA occA r⊢
  composeʷ {C = .★} comp (inst nonvarA occA p B≢★) q
      | r , r⊢ | yes refl | s , s⊢
      with wrap-tag★⇒★ (inst nonvarA occA s⊢ (λ ()))
  composeʷ {C = .★} comp (inst nonvarA occA p B≢★) q
      | r , r⊢ | yes refl | s , s⊢ | t , t⊢ =
    t , t⊢
  composeʷ {C = C} comp (inst nonvarA occA p B≢★) q
      | r , r⊢ | no C≢★ =
    Coercions.inst r , inst nonvarA occA r⊢ C≢★
  composeʷ comp (p₁ ↦ p₂) (q₁ ↦ q₂)
      with composeⁿ comp q₁ p₁ | composeʷ comp p₂ q₂
  composeʷ comp (p₁ ↦ p₂) (q₁ ↦ q₂)
      | r₁ , r₁⊢ | r₂ , r₂⊢ =
    r₁ ↦ᶜ r₂ , (r₁⊢ ↦ r₂⊢)
  composeʷ comp (∀ʷ p) (∀ʷ q)
      with composeʷ (compose-all comp) p q
  composeʷ comp (∀ʷ p) (∀ʷ q) | r , r⊢ =
    ∀ᶜ r , ∀ʷ r⊢

------------------------------------------------------------------------
-- Public two-context composition
------------------------------------------------------------------------

narrowing-composition-total : ∀ {c d Φ Δᴸ Δᴿ A B C}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ
narrowing-composition-total {Φ = Φ} {Δᴿ = Δᴿ} =
  composeⁿ (compose-id-left Δᴿ Φ)

widening-composition-total : ∀ {c d Φ Δᴸ Δᴿ A B C}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ d ⦂ B ⊑ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ
widening-composition-total {Φ = Φ} {Δᴸ = Δᴸ} =
  composeʷ (compose-id-left Δᴸ Φ)
