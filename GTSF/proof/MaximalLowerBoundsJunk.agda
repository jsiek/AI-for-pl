module proof.MaximalLowerBoundsJunk where

-- File Charter:
--   * Junk drawer for the old shape-directed `choose-mlb` attempt.
--   * Kept as a reference while `proof.MaximalLowerBounds` pivots to a
--     generalized lower-bound theorem.
--   * Do not import this module from the active compiler/metatheory path.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (¬_)

open import Types
open import Imprecision
  using
    ( ImpAssm
    ; ImpCtx
    ; _ˣ⊑★
    ; _ˣ⊑ˣ_
    ; ⇑ᵢ
    ; ⇑ᴸᵢ
    ; idᵢ
    ; _⊢_⊑_
    ; _⊢_~_
    ; id★
    ; idˣ
    ; idι
    ; _↦_
    ; ∀ⁱ_
    ; tag_
    ; tagˣ_
    ; tag_⇒_
    ; ν
    )
open import proof.ImprecisionProperties using (⊑-refl-idᵢ; ⊑-tgt-wf-idᵢ)

------------------------------------------------------------------------
-- Maximal lower bounds
------------------------------------------------------------------------

CommonLowerBound : TyCtx → Ty → Ty → Ty → Set
CommonLowerBound Δ A B C =
  idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B

StrictlyBelow : TyCtx → Ty → Ty → Set
StrictlyBelow Δ C D =
  idᵢ Δ ⊢ C ⊑ D × ¬ (idᵢ Δ ⊢ D ⊑ C)

record MaximalLowerBound (Δ : TyCtx) (A B : Ty) : Set where
  field
    lower : Ty
    lower-left : idᵢ Δ ⊢ lower ⊑ A
    lower-right : idᵢ Δ ⊢ lower ⊑ B
    maximal :
      ∀ {D} →
      CommonLowerBound Δ A B D →
      ¬ StrictlyBelow Δ lower D

open MaximalLowerBound public

------------------------------------------------------------------------
-- Generalized lower bounds
------------------------------------------------------------------------

-- PolyConvert's `Glbᶜ` keeps separate imprecision contexts for the left
-- lower-bound proof, the right lower-bound proof, and the output comparison.
-- The polymorphic cases need the same shape because `∀ⁱ` and `ν` extend the
-- assumption context in different ways.

CommonLowerBoundᶜ : ImpCtx → ImpCtx → Ty → Ty → Ty → Set
CommonLowerBoundᶜ Φᴸ Φᴿ A B C =
  Φᴸ ⊢ C ⊑ A × Φᴿ ⊢ C ⊑ B

StrictlyBelowᶜ : ImpCtx → Ty → Ty → Set
StrictlyBelowᶜ Φ C D =
  Φ ⊢ C ⊑ D × ¬ (Φ ⊢ D ⊑ C)

record MaximalLowerBoundᶜ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B : Ty) : Set where
  field
    lowerᶜ : Ty
    lower-leftᶜ : Φᴸ ⊢ lowerᶜ ⊑ A
    lower-rightᶜ : Φᴿ ⊢ lowerᶜ ⊑ B
    maximalᶜ :
      ∀ {D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ A B D →
      ¬ StrictlyBelowᶜ Φᴼ lowerᶜ D

open MaximalLowerBoundᶜ public

------------------------------------------------------------------------
-- Identity imprecision context facts
------------------------------------------------------------------------

⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
⇑ᵢ-ˣ∈ {Φ = []} ()
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᵢ-ˣ∈ x∈)
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᵢ-ˣ∈ x∈)

⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
⇑ᵢ-★∈ {Φ = []} ()
⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᵢ-★∈ x∈)
⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᵢ-★∈ x∈)

un⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᵢ-ˣ∈ {Φ = []} ()
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-ˣ∈ x∈)
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-ˣ∈ x∈)

un⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᵢ-★∈ {Φ = []} ()
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-★∈ x∈)
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-★∈ x∈)

no-⇑ᵢ-zero-left :
  ∀ {Φ X} →
  (zero ˣ⊑ˣ X) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-left {Φ = []} ()
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-left x∈
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-left x∈

no-⇑ᵢ-zero-right :
  ∀ {Φ X} →
  (X ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-right {Φ = []} ()
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-right x∈
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-right x∈

no-⇑ᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-star {Φ = []} ()
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-star x∈
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-star x∈

no-⇑ᴸᵢ-zero-left :
  ∀ {Φ X} →
  (zero ˣ⊑ˣ X) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-left {Φ = []} ()
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈

no-νctx-zero-var :
  ∀ {Φ X} →
  (zero ˣ⊑ˣ X) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  ⊥
no-νctx-zero-var (here ())
no-νctx-zero-var (there x∈) = no-⇑ᴸᵢ-zero-left x∈

idᵢ-refl-∈ :
  ∀ {Δ X} →
  X < Δ →
  (X ˣ⊑ˣ X) ∈ idᵢ Δ
idᵢ-refl-∈ {Δ = suc Δ} {X = zero} z<s = here refl
idᵢ-refl-∈ {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (⇑ᵢ-ˣ∈ (idᵢ-refl-∈ X<Δ))

idᵢ-var-identity :
  ∀ {Δ X Y} →
  (X ˣ⊑ˣ Y) ∈ idᵢ Δ →
  X ≡ Y
idᵢ-var-identity {Δ = zero} ()
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero} (here refl) =
  refl
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = suc Y} (there x∈) =
  cong suc (idᵢ-var-identity (un⇑ᵢ-ˣ∈ x∈))

idᵢ-var-left-bound :
  ∀ {Δ X Y} →
  (X ˣ⊑ˣ Y) ∈ idᵢ Δ →
  X < Δ
idᵢ-var-left-bound {Δ = zero} ()
idᵢ-var-left-bound {Δ = suc Δ} {X = zero} (here refl) = z<s
idᵢ-var-left-bound {Δ = suc Δ} {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
idᵢ-var-left-bound {Δ = suc Δ} {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
idᵢ-var-left-bound {Δ = suc Δ} {X = suc X} {Y = suc Y} (there x∈) =
  s<s (idᵢ-var-left-bound (un⇑ᵢ-ˣ∈ x∈))

idᵢ-no-star :
  ∀ {Δ X} →
  (X ˣ⊑★) ∈ idᵢ Δ →
  ⊥
idᵢ-no-star {Δ = zero} ()
idᵢ-no-star {Δ = suc Δ} {X = zero} (there x∈) =
  no-⇑ᵢ-zero-star x∈
idᵢ-no-star {Δ = suc Δ} {X = suc X} (there x∈) =
  idᵢ-no-star (un⇑ᵢ-★∈ x∈)

------------------------------------------------------------------------
-- Small inversions for impossible easy shape cases
------------------------------------------------------------------------

no-occurs-base-lower :
  ∀ {Φ A ι} →
  occurs zero A ≡ true →
  Φ ⊢ A ⊑ ‵ ι →
  ⊥
no-occurs-base-lower () idι
no-occurs-base-lower occ (ν occA p) =
  no-occurs-base-lower occA p

no-occurs-var-lower-νctx :
  ∀ {Φ A X} →
  occurs zero A ≡ true →
  (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ ＇ X →
  ⊥
no-occurs-var-lower-νctx {A = ＇ zero} occ (idˣ x∈) =
  no-νctx-zero-var x∈
no-occurs-var-lower-νctx {A = ＇ suc X} () (idˣ x∈)
no-occurs-var-lower-νctx occ (ν occA p) =
  no-occurs-var-lower-νctx occA p

------------------------------------------------------------------------
-- Comparable maximal lower bounds
------------------------------------------------------------------------

record ComparableMaximalLowerBound
    (Δ : TyCtx) (A B : Ty) : Set where
  field
    c-lower : Ty
    c-lower-left : idᵢ Δ ⊢ c-lower ⊑ A
    c-lower-right : idᵢ Δ ⊢ c-lower ⊑ B
    c-comparable :
      ∀ {D} →
      CommonLowerBound Δ A B D →
      idᵢ Δ ⊢ c-lower ⊑ D →
      idᵢ Δ ⊢ D ⊑ c-lower

open ComparableMaximalLowerBound public

comparable⇒maximal :
  ∀ {Δ A B} →
  ComparableMaximalLowerBound Δ A B →
  MaximalLowerBound Δ A B
comparable⇒maximal cb =
  record
    { lower = c-lower cb
    ; lower-left = c-lower-left cb
    ; lower-right = c-lower-right cb
    ; maximal = λ common (lower⊑D , ¬D⊑lower) →
        ¬D⊑lower (c-comparable cb common lower⊑D)
    }

------------------------------------------------------------------------
-- Base, star, and variable cases
------------------------------------------------------------------------

comparable-star-star :
  ∀ {Δ} →
  ComparableMaximalLowerBound Δ ★ ★
comparable-star-star =
  record
    { c-lower = ★
    ; c-lower-left = id★
    ; c-lower-right = id★
    ; c-comparable = λ common id★ → proj₁ common
    }

maximal-star-star :
  ∀ {Δ} →
  MaximalLowerBound Δ ★ ★
maximal-star-star = comparable⇒maximal comparable-star-star

comparable-base-base :
  ∀ {Δ ι} →
  ComparableMaximalLowerBound Δ (‵ ι) (‵ ι)
comparable-base-base =
  record
    { c-lower = ‵ _
    ; c-lower-left = idι
    ; c-lower-right = idι
    ; c-comparable = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBound Δ (‵ ι) (‵ ι) D →
      idᵢ Δ ⊢ ‵ ι ⊑ D →
      idᵢ Δ ⊢ D ⊑ ‵ ι
    comparable common idι = proj₁ common
    comparable (() , _) (tag ι)

maximal-base-base :
  ∀ {Δ ι} →
  MaximalLowerBound Δ (‵ ι) (‵ ι)
maximal-base-base = comparable⇒maximal comparable-base-base

comparable-base-star :
  ∀ {Δ ι} →
  ComparableMaximalLowerBound Δ (‵ ι) ★
comparable-base-star =
  record
    { c-lower = ‵ _
    ; c-lower-left = idι
    ; c-lower-right = tag _
    ; c-comparable = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBound Δ (‵ ι) ★ D →
      idᵢ Δ ⊢ ‵ ι ⊑ D →
      idᵢ Δ ⊢ D ⊑ ‵ ι
    comparable common idι = proj₁ common
    comparable (() , _) (tag ι)

maximal-base-star :
  ∀ {Δ ι} →
  MaximalLowerBound Δ (‵ ι) ★
maximal-base-star = comparable⇒maximal comparable-base-star

comparable-star-base :
  ∀ {Δ ι} →
  ComparableMaximalLowerBound Δ ★ (‵ ι)
comparable-star-base =
  record
    { c-lower = ‵ _
    ; c-lower-left = tag _
    ; c-lower-right = idι
    ; c-comparable = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBound Δ ★ (‵ ι) D →
      idᵢ Δ ⊢ ‵ ι ⊑ D →
      idᵢ Δ ⊢ D ⊑ ‵ ι
    comparable common idι = proj₂ common
    comparable (_ , ()) (tag ι)

maximal-star-base :
  ∀ {Δ ι} →
  MaximalLowerBound Δ ★ (‵ ι)
maximal-star-base = comparable⇒maximal comparable-star-base

comparable-var-var :
  ∀ {Δ X} →
  X < Δ →
  ComparableMaximalLowerBound Δ (＇ X) (＇ X)
comparable-var-var {Δ} {X} X<Δ =
  record
    { c-lower = ＇ X
    ; c-lower-left = idˣ (idᵢ-refl-∈ X<Δ)
    ; c-lower-right = idˣ (idᵢ-refl-∈ X<Δ)
    ; c-comparable = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBound Δ (＇ X) (＇ X) D →
      idᵢ Δ ⊢ ＇ X ⊑ D →
      idᵢ Δ ⊢ D ⊑ ＇ X
    comparable common (idˣ x∈)
      rewrite idᵢ-var-identity x∈ = proj₁ common
    comparable common (tagˣ x∈) = ⊥-elim (idᵢ-no-star x∈)

maximal-var-var :
  ∀ {Δ X} →
  X < Δ →
  MaximalLowerBound Δ (＇ X) (＇ X)
maximal-var-var X<Δ = comparable⇒maximal (comparable-var-var X<Δ)

------------------------------------------------------------------------
-- Arrow composition
------------------------------------------------------------------------

comparable-arrow-arrow :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBound Δ A₁ B₁ →
  ComparableMaximalLowerBound Δ A₂ B₂ →
  ComparableMaximalLowerBound Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
comparable-arrow-arrow c₁ c₂ =
  record
    { c-lower = c-lower c₁ ⇒ c-lower c₂
    ; c-lower-left = c-lower-left c₁ ↦ c-lower-left c₂
    ; c-lower-right = c-lower-right c₁ ↦ c-lower-right c₂
    ; c-comparable = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBound _ (_ ⇒ _) (_ ⇒ _) D →
      idᵢ _ ⊢ c-lower c₁ ⇒ c-lower c₂ ⊑ D →
      idᵢ _ ⊢ D ⊑ c-lower c₁ ⇒ c-lower c₂
    comparable ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      c-comparable c₁ (D₁⊑A₁ , D₁⊑B₁) C₁⊑D₁ ↦
      c-comparable c₂ (D₂⊑A₂ , D₂⊑B₂) C₂⊑D₂
    comparable (() , _) (tag_⇒_ C₁⊑★ C₂⊑★)

maximal-arrow-arrow :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBound Δ A₁ B₁ →
  ComparableMaximalLowerBound Δ A₂ B₂ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow c₁ c₂ =
  comparable⇒maximal (comparable-arrow-arrow c₁ c₂)

postulate
  arrow-arrow-domain-consistent-ν :
    ∀ {Δ C A₁ A₂ B₁ B₂} →
    idᵢ Δ ⊢ `∀ C ⊑ A₁ ⇒ A₂ →
    idᵢ Δ ⊢ `∀ C ⊑ B₁ ⇒ B₂ →
    Δ ⊢ A₁ ~ B₁

  arrow-arrow-codomain-consistent-ν :
    ∀ {Δ C A₁ A₂ B₁ B₂} →
    idᵢ Δ ⊢ `∀ C ⊑ A₁ ⇒ A₂ →
    idᵢ Δ ⊢ `∀ C ⊑ B₁ ⇒ B₂ →
    Δ ⊢ A₂ ~ B₂

  star-arrow-domain-consistent-ν :
    ∀ {Δ C B₁ B₂} →
    idᵢ Δ ⊢ `∀ C ⊑ ★ →
    idᵢ Δ ⊢ `∀ C ⊑ B₁ ⇒ B₂ →
    Δ ⊢ ★ ~ B₁

  star-arrow-codomain-consistent-ν :
    ∀ {Δ C B₁ B₂} →
    idᵢ Δ ⊢ `∀ C ⊑ ★ →
    idᵢ Δ ⊢ `∀ C ⊑ B₁ ⇒ B₂ →
    Δ ⊢ ★ ~ B₂

maximal-arrow-arrow-from-maximal :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  MaximalLowerBound Δ A₁ B₁ →
  MaximalLowerBound Δ A₂ B₂ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow-from-maximal mlb₁ mlb₂ =
  record
    { lower = lower mlb₁ ⇒ lower mlb₂
    ; lower-left = lower-left mlb₁ ↦ lower-left mlb₂
    ; lower-right = lower-right mlb₁ ↦ lower-right mlb₂
    ; maximal = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBound _ (_ ⇒ _) (_ ⇒ _) D →
      ¬ StrictlyBelow _ (lower mlb₁ ⇒ lower mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximal mlb₁ (D₁⊑A₁ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximal mlb₂ (D₂⊑A₂ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (() , _) ((tag_⇒_ C₁⊑★ C₂⊑★) , ¬D⊑C)

arrow-arrow-domain-consistent :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  Δ ⊢ (A₁ ⇒ A₂) ~ (B₁ ⇒ B₂) →
  Δ ⊢ A₁ ~ B₁
arrow-arrow-domain-consistent
    (C , (C₁⊑A₁ ↦ C₂⊑A₂) , (C₁⊑B₁ ↦ C₂⊑B₂)) =
  _ , C₁⊑A₁ , C₁⊑B₁
arrow-arrow-domain-consistent (`∀ C , C⊑A , C⊑B) =
  arrow-arrow-domain-consistent-ν C⊑A C⊑B

arrow-arrow-codomain-consistent :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  Δ ⊢ (A₁ ⇒ A₂) ~ (B₁ ⇒ B₂) →
  Δ ⊢ A₂ ~ B₂
arrow-arrow-codomain-consistent
    (C , (C₁⊑A₁ ↦ C₂⊑A₂) , (C₁⊑B₁ ↦ C₂⊑B₂)) =
  _ , C₂⊑A₂ , C₂⊑B₂
arrow-arrow-codomain-consistent (`∀ C , C⊑A , C⊑B) =
  arrow-arrow-codomain-consistent-ν C⊑A C⊑B

~-sym :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  Δ ⊢ B ~ A
~-sym (C , C⊑A , C⊑B) = C , C⊑B , C⊑A

star-arrow-domain-consistent :
  ∀ {Δ B₁ B₂} →
  Δ ⊢ ★ ~ B₁ ⇒ B₂ →
  Δ ⊢ ★ ~ B₁
star-arrow-domain-consistent
    (C₁ ⇒ C₂ , tag_⇒_ C₁⊑★ C₂⊑★ , C₁⊑B₁ ↦ C₂⊑B₂) =
  C₁ , C₁⊑★ , C₁⊑B₁
star-arrow-domain-consistent (`∀ C , C⊑★ , C⊑B) =
  star-arrow-domain-consistent-ν C⊑★ C⊑B

star-arrow-codomain-consistent :
  ∀ {Δ B₁ B₂} →
  Δ ⊢ ★ ~ B₁ ⇒ B₂ →
  Δ ⊢ ★ ~ B₂
star-arrow-codomain-consistent
    (C₁ ⇒ C₂ , tag_⇒_ C₁⊑★ C₂⊑★ , C₁⊑B₁ ↦ C₂⊑B₂) =
  C₂ , C₂⊑★ , C₂⊑B₂
star-arrow-codomain-consistent (`∀ C , C⊑★ , C⊑B) =
  star-arrow-codomain-consistent-ν C⊑★ C⊑B

arrow-star-domain-consistent :
  ∀ {Δ A₁ A₂} →
  Δ ⊢ A₁ ⇒ A₂ ~ ★ →
  Δ ⊢ A₁ ~ ★
arrow-star-domain-consistent A~★ =
  ~-sym (star-arrow-domain-consistent (~-sym A~★))

arrow-star-codomain-consistent :
  ∀ {Δ A₁ A₂} →
  Δ ⊢ A₁ ⇒ A₂ ~ ★ →
  Δ ⊢ A₂ ~ ★
arrow-star-codomain-consistent A~★ =
  ~-sym (star-arrow-codomain-consistent (~-sym A~★))

maximal-star-arrow-from-maximal :
  ∀ {Δ B₁ B₂} →
  MaximalLowerBound Δ ★ B₁ →
  MaximalLowerBound Δ ★ B₂ →
  MaximalLowerBound Δ ★ (B₁ ⇒ B₂)
maximal-star-arrow-from-maximal mlb₁ mlb₂ =
  record
    { lower = lower mlb₁ ⇒ lower mlb₂
    ; lower-left = tag_⇒_ (lower-left mlb₁) (lower-left mlb₂)
    ; lower-right = lower-right mlb₁ ↦ lower-right mlb₂
    ; maximal = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBound _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelow _ (lower mlb₁ ⇒ lower mlb₂) D
    maximal′ ((tag_⇒_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximal mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximal mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇒_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximal :
  ∀ {Δ A₁ A₂} →
  MaximalLowerBound Δ A₁ ★ →
  MaximalLowerBound Δ A₂ ★ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximal mlb₁ mlb₂ =
  record
    { lower = lower mlb₁ ⇒ lower mlb₂
    ; lower-left = lower-left mlb₁ ↦ lower-left mlb₂
    ; lower-right = tag_⇒_ (lower-right mlb₁) (lower-right mlb₂)
    ; maximal = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBound _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelow _ (lower mlb₁ ⇒ lower mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇒_ D₁⊑★ D₂⊑★))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximal mlb₁ (D₁⊑A₁ , D₁⊑★)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximal mlb₂ (D₂⊑A₂ , D₂⊑★)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (() , id★) ((tag_⇒_ C₁⊑★ C₂⊑★) , ¬D⊑C)

------------------------------------------------------------------------
-- Shape-directed selector skeleton
------------------------------------------------------------------------

-- This dispatcher is the maximal-lower-bound analogue of PolyConvert's
-- `glb?`: split on the outer type constructors, solve the simple closed
-- cases immediately, and leave each remaining branch as a named obligation.
-- The `forall` rows are where the old `split-∀`/`lift-search⁺` strategy has to
-- be relaxed from "find a GLB" to "choose a deterministic maximal lower bound".

wf∀-occ :
  ∀ {Δ A} →
  WfTy Δ (`∀ A) →
  occurs zero A ≡ true
wf∀-occ (wf∀ {occ = occ} hA) = occ

data ForallForallLower² (Δ : TyCtx) (C A B : Ty) : Set where
  via-∀∀ :
    {occC : occurs zero C ≡ true} →
    {occA : occurs zero A ≡ true} →
    {occB : occurs zero B ≡ true} →
    idᵢ (suc Δ) ⊢ C ⊑ A →
    idᵢ (suc Δ) ⊢ C ⊑ B →
    ForallForallLower² Δ C A B

  via-∀ν :
    {occC : occurs zero C ≡ true} →
    {occA : occurs zero A ≡ true} →
    {occB : occurs zero B ≡ true} →
    idᵢ (suc Δ) ⊢ C ⊑ A →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ B) →
    ForallForallLower² Δ C A B

  via-ν∀ :
    {occC : occurs zero C ≡ true} →
    {occA : occurs zero A ≡ true} →
    {occB : occurs zero B ≡ true} →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    idᵢ (suc Δ) ⊢ C ⊑ B →
    ForallForallLower² Δ C A B

  via-νν :
    {occC : occurs zero C ≡ true} →
    {occA : occurs zero A ≡ true} →
    {occB : occurs zero B ≡ true} →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ B) →
    ForallForallLower² Δ C A B

postulate
  forall-common-star⇒star :
    ∀ {Δ C A} →
    idᵢ Δ ⊢ C ⊑ `∀ A →
    idᵢ Δ ⊢ C ⊑ ★ →
    idᵢ Δ ⊢ `∀ A ⊑ ★

  choose-mlb-arrow-forall-ν∀ :
    ∀ {Δ A₁ A₂ B} →
    ∀ {C} →
    occurs zero C ≡ true →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (A₁ ⇒ A₂) →
    idᵢ (suc Δ) ⊢ C ⊑ B →
    MaximalLowerBound Δ (A₁ ⇒ A₂) (`∀ B)

  choose-mlb-arrow-forall-νν :
    ∀ {Δ A₁ A₂ B} →
    ∀ {C} →
    occurs zero C ≡ true →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (A₁ ⇒ A₂) →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ B) →
    MaximalLowerBound Δ (A₁ ⇒ A₂) (`∀ B)

  choose-mlb-forall-arrow-∀ν :
    ∀ {Δ A B₁ B₂} →
    ∀ {C} →
    idᵢ (suc Δ) ⊢ C ⊑ A →
    occurs zero C ≡ true →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (B₁ ⇒ B₂) →
    MaximalLowerBound Δ (`∀ A) (B₁ ⇒ B₂)

  choose-mlb-forall-arrow-νν :
    ∀ {Δ A B₁ B₂} →
    ∀ {C} →
    occurs zero C ≡ true →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (B₁ ⇒ B₂) →
    MaximalLowerBound Δ (`∀ A) (B₁ ⇒ B₂)

  choose-mlb-forall-forall-split :
    ∀ {Δ A B C} →
    ForallForallLower² Δ C A B →
    MaximalLowerBound Δ (`∀ A) (`∀ B)

choose-mlb-forall-forall-∀∀ :
  ∀ {Δ A B C}
    {occC : occurs zero C ≡ true}
    {occA : occurs zero A ≡ true}
    {occB : occurs zero B ≡ true} →
  idᵢ (suc Δ) ⊢ C ⊑ A →
  idᵢ (suc Δ) ⊢ C ⊑ B →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall-∀∀
    {occC = occC} {occA = occA} {occB = occB} C⊑A C⊑B =
  choose-mlb-forall-forall-split
    (via-∀∀ {occC = occC} {occA = occA} {occB = occB} C⊑A C⊑B)

choose-mlb-forall-forall-∀ν :
  ∀ {Δ A B C}
    {occA : occurs zero A ≡ true} →
  idᵢ (suc Δ) ⊢ C ⊑ A →
  occurs zero C ≡ true →
  (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ B) →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall-∀ν {occA = occA} C⊑A occC C⊑B =
  choose-mlb-forall-forall-split
    (via-∀ν {occC = occC}
            {occA = occA}
            {occB = wf∀-occ (⊑-tgt-wf-idᵢ (ν occC C⊑B))}
            C⊑A C⊑B)

choose-mlb-forall-forall-ν∀ :
  ∀ {Δ A B C}
    {occB : occurs zero B ≡ true} →
  occurs zero C ≡ true →
  (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
  idᵢ (suc Δ) ⊢ C ⊑ B →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall-ν∀ {occB = occB} occC C⊑A C⊑B =
  choose-mlb-forall-forall-split
    (via-ν∀ {occC = occC}
            {occA = wf∀-occ (⊑-tgt-wf-idᵢ (ν occC C⊑A))}
            {occB = occB}
            C⊑A C⊑B)

choose-mlb-forall-forall-νν :
  ∀ {Δ A B C} →
  occurs zero C ≡ true →
  (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
  (zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ B) →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall-νν occC C⊑A C⊑B =
  choose-mlb-forall-forall-split
    (via-νν {occC = occC}
            {occA = wf∀-occ (⊑-tgt-wf-idᵢ (ν occC C⊑A))}
            {occB = wf∀-occ (⊑-tgt-wf-idᵢ (ν occC C⊑B))}
            C⊑A C⊑B)

choose-mlb-star-forall :
  ∀ {Δ B} →
  Δ ⊢ ★ ~ `∀ B →
  MaximalLowerBound Δ ★ (`∀ B)
choose-mlb-star-forall {B = B} (_ , C⊑★ , C⊑∀B) =
  record
    { lower = `∀ B
    ; lower-left = forall-common-star⇒star C⊑∀B C⊑★
    ; lower-right = ⊑-refl-idᵢ (⊑-tgt-wf-idᵢ C⊑∀B)
    ; maximal = λ common (_ , ¬D⊑∀B) → ¬D⊑∀B (proj₂ common)
    }

choose-mlb-forall-star :
  ∀ {Δ A} →
  Δ ⊢ `∀ A ~ ★ →
  MaximalLowerBound Δ (`∀ A) ★
choose-mlb-forall-star {A = A} (_ , C⊑∀A , C⊑★) =
  record
    { lower = `∀ A
    ; lower-left = ⊑-refl-idᵢ (⊑-tgt-wf-idᵢ C⊑∀A)
    ; lower-right = forall-common-star⇒star C⊑∀A C⊑★
    ; maximal = λ common (_ , ¬D⊑∀A) → ¬D⊑∀A (proj₁ common)
    }

choose-mlb-var-var :
  ∀ {Δ X Y} →
  Δ ⊢ ＇ X ~ ＇ Y →
  MaximalLowerBound Δ (＇ X) (＇ Y)
choose-mlb-var-var {Δ} {X} {Y} (_ , idˣ {X = z} z⊑X , idˣ z⊑Y)
    with idᵢ-var-identity z⊑X | idᵢ-var-identity z⊑Y
choose-mlb-var-var {Δ} {X} {Y} (_ , idˣ {X = z} z⊑X , idˣ z⊑Y)
    | refl | refl =
  maximal-var-var (idᵢ-var-left-bound z⊑X)
choose-mlb-var-var (_ , ν occA A⊑X , C⊑Y) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑X)

choose-mlb-var-star :
  ∀ {Δ X} →
  Δ ⊢ ＇ X ~ ★ →
  MaximalLowerBound Δ (＇ X) ★
choose-mlb-var-star (_ , idˣ Z⊑X , tagˣ Z⊑★) =
  ⊥-elim (idᵢ-no-star Z⊑★)
choose-mlb-var-star (_ , ν occA A⊑X , C⊑★) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑X)

choose-mlb-star-var :
  ∀ {Δ Y} →
  Δ ⊢ ★ ~ ＇ Y →
  MaximalLowerBound Δ ★ (＇ Y)
choose-mlb-star-var (_ , tagˣ Z⊑★ , idˣ Z⊑Y) =
  ⊥-elim (idᵢ-no-star Z⊑★)
choose-mlb-star-var (_ , C⊑★ , ν occA A⊑Y) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑Y)

choose-mlb-var-arrow :
  ∀ {Δ X B₁ B₂} →
  Δ ⊢ ＇ X ~ (B₁ ⇒ B₂) →
  MaximalLowerBound Δ (＇ X) (B₁ ⇒ B₂)
choose-mlb-var-arrow (_ , idˣ z⊑X , ())
choose-mlb-var-arrow (_ , ν occA A⊑X , C⊑B) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑X)

choose-mlb-arrow-var :
  ∀ {Δ A₁ A₂ Y} →
  Δ ⊢ (A₁ ⇒ A₂) ~ ＇ Y →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (＇ Y)
choose-mlb-arrow-var (_ , () , idˣ z⊑Y)
choose-mlb-arrow-var (_ , C⊑A , ν occB B⊑Y) =
  ⊥-elim (no-occurs-var-lower-νctx occB B⊑Y)

choose-mlb-var-forall :
  ∀ {Δ X B} →
  Δ ⊢ ＇ X ~ `∀ B →
  MaximalLowerBound Δ (＇ X) (`∀ B)
choose-mlb-var-forall (_ , idˣ z⊑X , ())
choose-mlb-var-forall (_ , ν occA A⊑X , C⊑∀B) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑X)

choose-mlb-forall-var :
  ∀ {Δ A Y} →
  Δ ⊢ `∀ A ~ ＇ Y →
  MaximalLowerBound Δ (`∀ A) (＇ Y)
choose-mlb-forall-var (_ , () , idˣ z⊑Y)
choose-mlb-forall-var (_ , C⊑∀A , ν occB B⊑Y) =
  ⊥-elim (no-occurs-var-lower-νctx occB B⊑Y)

choose-mlb-var-base :
  ∀ {Δ X ι} →
  Δ ⊢ ＇ X ~ ‵ ι →
  MaximalLowerBound Δ (＇ X) (‵ ι)
choose-mlb-var-base (_ , idˣ Z⊑X , ())
choose-mlb-var-base (_ , ν occA A⊑X , C⊑ι) =
  ⊥-elim (no-occurs-var-lower-νctx occA A⊑X)

choose-mlb-base-var :
  ∀ {Δ ι Y} →
  Δ ⊢ ‵ ι ~ ＇ Y →
  MaximalLowerBound Δ (‵ ι) (＇ Y)
choose-mlb-base-var (_ , idι , ())
choose-mlb-base-var (_ , ν occA A⊑ι , C⊑Y) =
  ⊥-elim (no-occurs-base-lower occA A⊑ι)

choose-mlb-base-base :
  ∀ {Δ ι κ} →
  Δ ⊢ ‵ ι ~ ‵ κ →
  MaximalLowerBound Δ (‵ ι) (‵ κ)
choose-mlb-base-base (_ , idι , idι) = maximal-base-base
choose-mlb-base-base (_ , ν occA A⊑ι , C⊑κ) =
  ⊥-elim (no-occurs-base-lower occA A⊑ι)

choose-mlb-base-arrow :
  ∀ {Δ ι B₁ B₂} →
  Δ ⊢ ‵ ι ~ (B₁ ⇒ B₂) →
  MaximalLowerBound Δ (‵ ι) (B₁ ⇒ B₂)
choose-mlb-base-arrow (_ , idι , ())
choose-mlb-base-arrow (_ , ν occA A⊑ι , C⊑B) =
  ⊥-elim (no-occurs-base-lower occA A⊑ι)

choose-mlb-arrow-base :
  ∀ {Δ A₁ A₂ κ} →
  Δ ⊢ (A₁ ⇒ A₂) ~ ‵ κ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (‵ κ)
choose-mlb-arrow-base (_ , () , idι)
choose-mlb-arrow-base (_ , C⊑A , ν occB B⊑κ) =
  ⊥-elim (no-occurs-base-lower occB B⊑κ)

choose-mlb-arrow-forall-from-lower :
  ∀ {Δ A₁ A₂ B C} →
  idᵢ Δ ⊢ C ⊑ A₁ ⇒ A₂ →
  idᵢ Δ ⊢ C ⊑ `∀ B →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (`∀ B)
choose-mlb-arrow-forall-from-lower (p ↦ q) ()
choose-mlb-arrow-forall-from-lower (ν occC C⊑A) (∀ⁱ C⊑B) =
  choose-mlb-arrow-forall-ν∀ occC C⊑A C⊑B
choose-mlb-arrow-forall-from-lower (ν occC C⊑A) (ν _ C⊑B) =
  choose-mlb-arrow-forall-νν occC C⊑A C⊑B

choose-mlb-arrow-forall :
  ∀ {Δ A₁ A₂ B} →
  Δ ⊢ (A₁ ⇒ A₂) ~ `∀ B →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (`∀ B)
choose-mlb-arrow-forall (C , C⊑A , C⊑B) =
  choose-mlb-arrow-forall-from-lower C⊑A C⊑B

choose-mlb-forall-arrow-from-lower :
  ∀ {Δ A B₁ B₂ C} →
  idᵢ Δ ⊢ C ⊑ `∀ A →
  idᵢ Δ ⊢ C ⊑ B₁ ⇒ B₂ →
  MaximalLowerBound Δ (`∀ A) (B₁ ⇒ B₂)
choose-mlb-forall-arrow-from-lower (∀ⁱ C⊑A) (ν occC C⊑B) =
  choose-mlb-forall-arrow-∀ν C⊑A occC C⊑B
choose-mlb-forall-arrow-from-lower (ν occC C⊑A) (ν _ C⊑B) =
  choose-mlb-forall-arrow-νν occC C⊑A C⊑B

choose-mlb-forall-arrow :
  ∀ {Δ A B₁ B₂} →
  Δ ⊢ `∀ A ~ (B₁ ⇒ B₂) →
  MaximalLowerBound Δ (`∀ A) (B₁ ⇒ B₂)
choose-mlb-forall-arrow (C , C⊑A , C⊑B) =
  choose-mlb-forall-arrow-from-lower C⊑A C⊑B

choose-mlb-base-forall :
  ∀ {Δ ι B} →
  Δ ⊢ ‵ ι ~ `∀ B →
  MaximalLowerBound Δ (‵ ι) (`∀ B)
choose-mlb-base-forall (_ , idι , ())
choose-mlb-base-forall (_ , ν occA A⊑ι , C⊑∀B) =
  ⊥-elim (no-occurs-base-lower occA A⊑ι)

choose-mlb-forall-base :
  ∀ {Δ A κ} →
  Δ ⊢ `∀ A ~ ‵ κ →
  MaximalLowerBound Δ (`∀ A) (‵ κ)
choose-mlb-forall-base (_ , () , idι)
choose-mlb-forall-base (_ , C⊑∀A , ν occB B⊑κ) =
  ⊥-elim (no-occurs-base-lower occB B⊑κ)

choose-mlb-forall-forall-from-lower :
  ∀ {Δ A B C} →
  idᵢ Δ ⊢ C ⊑ `∀ A →
  idᵢ Δ ⊢ C ⊑ `∀ B →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall-from-lower
    (∀ⁱ_ {occA = occC} {occB = occA} C⊑A)
    (∀ⁱ_ {occB = occB} C⊑B) =
  choose-mlb-forall-forall-∀∀
    {occC = occC} {occA = occA} {occB = occB} C⊑A C⊑B
choose-mlb-forall-forall-from-lower
    (∀ⁱ_ {occB = occA} C⊑A) (ν occC C⊑B) =
  choose-mlb-forall-forall-∀ν {occA = occA} C⊑A occC C⊑B
choose-mlb-forall-forall-from-lower
    (ν occC C⊑A) (∀ⁱ_ {occB = occB} C⊑B) =
  choose-mlb-forall-forall-ν∀ {occB = occB} occC C⊑A C⊑B
choose-mlb-forall-forall-from-lower (ν occC C⊑A) (ν _ C⊑B) =
  choose-mlb-forall-forall-νν occC C⊑A C⊑B

choose-mlb-forall-forall :
  ∀ {Δ A B} →
  Δ ⊢ `∀ A ~ `∀ B →
  MaximalLowerBound Δ (`∀ A) (`∀ B)
choose-mlb-forall-forall (C , C⊑A , C⊑B) =
  choose-mlb-forall-forall-from-lower C⊑A C⊑B

choose-mlb-base-star :
  ∀ {Δ ι} →
  Δ ⊢ ‵ ι ~ ★ →
  MaximalLowerBound Δ (‵ ι) ★
choose-mlb-base-star A~B = maximal-base-star

choose-mlb-star-base :
  ∀ {Δ κ} →
  Δ ⊢ ★ ~ ‵ κ →
  MaximalLowerBound Δ ★ (‵ κ)
choose-mlb-star-base A~B = maximal-star-base

choose-mlb-star-star :
  ∀ {Δ} →
  Δ ⊢ ★ ~ ★ →
  MaximalLowerBound Δ ★ ★
choose-mlb-star-star A~B = maximal-star-star

choose-mlb-shape :
  ∀ Δ A B →
  Δ ⊢ A ~ B →
  MaximalLowerBound Δ A B
choose-mlb-shape Δ (＇ X) (＇ Y) A~B =
  choose-mlb-var-var A~B
choose-mlb-shape Δ (＇ X) (‵ ι) A~B =
  choose-mlb-var-base A~B
choose-mlb-shape Δ (＇ X) ★ A~B =
  choose-mlb-var-star A~B
choose-mlb-shape Δ (＇ X) (B₁ ⇒ B₂) A~B =
  choose-mlb-var-arrow A~B
choose-mlb-shape Δ (＇ X) (`∀ B) A~B =
  choose-mlb-var-forall A~B
choose-mlb-shape Δ (‵ ι) (＇ Y) A~B =
  choose-mlb-base-var A~B
choose-mlb-shape Δ (‵ ι) (‵ κ) A~B =
  choose-mlb-base-base A~B
choose-mlb-shape Δ (‵ ι) ★ A~B =
  choose-mlb-base-star A~B
choose-mlb-shape Δ (‵ ι) (B₁ ⇒ B₂) A~B =
  choose-mlb-base-arrow A~B
choose-mlb-shape Δ (‵ ι) (`∀ B) A~B =
  choose-mlb-base-forall A~B
choose-mlb-shape Δ ★ (＇ Y) A~B =
  choose-mlb-star-var A~B
choose-mlb-shape Δ ★ (‵ κ) A~B =
  choose-mlb-star-base A~B
choose-mlb-shape Δ ★ ★ A~B =
  choose-mlb-star-star A~B
choose-mlb-shape Δ ★ (B₁ ⇒ B₂) A~B
    with choose-mlb-shape Δ ★ B₁ (star-arrow-domain-consistent A~B)
       | choose-mlb-shape Δ ★ B₂ (star-arrow-codomain-consistent A~B)
choose-mlb-shape Δ ★ (B₁ ⇒ B₂) A~B | mlb₁ | mlb₂ =
  maximal-star-arrow-from-maximal mlb₁ mlb₂
choose-mlb-shape Δ ★ (`∀ B) A~B =
  choose-mlb-star-forall A~B
choose-mlb-shape Δ (A₁ ⇒ A₂) (＇ Y) A~B =
  choose-mlb-arrow-var A~B
choose-mlb-shape Δ (A₁ ⇒ A₂) (‵ κ) A~B =
  choose-mlb-arrow-base A~B
choose-mlb-shape Δ (A₁ ⇒ A₂) ★ A~B
    with choose-mlb-shape Δ A₁ ★ (arrow-star-domain-consistent A~B)
       | choose-mlb-shape Δ A₂ ★ (arrow-star-codomain-consistent A~B)
choose-mlb-shape Δ (A₁ ⇒ A₂) ★ A~B | mlb₁ | mlb₂ =
  maximal-arrow-star-from-maximal mlb₁ mlb₂
choose-mlb-shape Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) A~B
    with choose-mlb-shape Δ A₁ B₁ (arrow-arrow-domain-consistent A~B)
       | choose-mlb-shape Δ A₂ B₂ (arrow-arrow-codomain-consistent A~B)
choose-mlb-shape Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) A~B | mlb₁ | mlb₂ =
  maximal-arrow-arrow-from-maximal mlb₁ mlb₂
choose-mlb-shape Δ (A₁ ⇒ A₂) (`∀ B) A~B =
  choose-mlb-arrow-forall A~B
choose-mlb-shape Δ (`∀ A) (＇ Y) A~B =
  choose-mlb-forall-var A~B
choose-mlb-shape Δ (`∀ A) (‵ κ) A~B =
  choose-mlb-forall-base A~B
choose-mlb-shape Δ (`∀ A) ★ A~B =
  choose-mlb-forall-star A~B
choose-mlb-shape Δ (`∀ A) (B₁ ⇒ B₂) A~B =
  choose-mlb-forall-arrow A~B
choose-mlb-shape Δ (`∀ A) (`∀ B) A~B =
  choose-mlb-forall-forall A~B

choose-mlb-star-arrow :
  ∀ {Δ B₁ B₂} →
  Δ ⊢ ★ ~ (B₁ ⇒ B₂) →
  MaximalLowerBound Δ ★ (B₁ ⇒ B₂)
choose-mlb-star-arrow {Δ} {B₁} {B₂} A~B =
  choose-mlb-shape Δ ★ (B₁ ⇒ B₂) A~B

choose-mlb-arrow-star :
  ∀ {Δ A₁ A₂} →
  Δ ⊢ (A₁ ⇒ A₂) ~ ★ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) ★
choose-mlb-arrow-star {Δ} {A₁} {A₂} A~B =
  choose-mlb-shape Δ (A₁ ⇒ A₂) ★ A~B

choose-mlb-arrow-arrow :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  Δ ⊢ (A₁ ⇒ A₂) ~ (B₁ ⇒ B₂) →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
choose-mlb-arrow-arrow {Δ} {A₁} {A₂} {B₁} {B₂} A~B =
  choose-mlb-shape Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) A~B

choose-mlb :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  MaximalLowerBound Δ A B
choose-mlb {Δ} {A} {B} A~B =
  choose-mlb-shape Δ A B A~B
