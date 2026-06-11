module proof.MaximalLowerBounds where

-- File Charter:
--   * Reusable maximal-lower-bound proof infrastructure for GTSF imprecision.
--   * Covers identity-context facts, base/star/type-variable maximality, and
--     arrow composition for lower bounds.
--   * Does not synthesize coercions or allocate stores.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; zero; suc; z<s; s<s; _≟_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Maybe using (Maybe; nothing; just)

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
-- Binder context modes
------------------------------------------------------------------------

data BinderMode : Set where
  ∀ᵇ : BinderMode
  νᵇ : BinderMode

liftCtx : BinderMode → ImpCtx → ImpCtx
liftCtx ∀ᵇ Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ
liftCtx νᵇ Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ

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

maximal-idᶜ :
  ∀ {Δ A B} →
  MaximalLowerBound Δ A B →
  MaximalLowerBoundᶜ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) A B
maximal-idᶜ mlb =
  record
    { lowerᶜ = lower mlb
    ; lower-leftᶜ = lower-left mlb
    ; lower-rightᶜ = lower-right mlb
    ; maximalᶜ = maximal mlb
    }

record ComparableMaximalLowerBoundᶜ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B : Ty) : Set where
  field
    cᶜ-lower : Ty
    cᶜ-lower-left : Φᴸ ⊢ cᶜ-lower ⊑ A
    cᶜ-lower-right : Φᴿ ⊢ cᶜ-lower ⊑ B
    cᶜ-comparable :
      ∀ {D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ A B D →
      Φᴼ ⊢ cᶜ-lower ⊑ D →
      Φᴼ ⊢ D ⊑ cᶜ-lower

open ComparableMaximalLowerBoundᶜ public

comparable⇒maximalᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ A B} →
  ComparableMaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A B →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A B
comparable⇒maximalᶜ cb =
  record
    { lowerᶜ = cᶜ-lower cb
    ; lower-leftᶜ = cᶜ-lower-left cb
    ; lower-rightᶜ = cᶜ-lower-right cb
    ; maximalᶜ = λ common (lower⊑D , ¬D⊑lower) →
        ¬D⊑lower (cᶜ-comparable cb common lower⊑D)
    }

comparable-star-starᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  ComparableMaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ ★
comparable-star-starᶜ =
  record
    { cᶜ-lower = ★
    ; cᶜ-lower-left = id★
    ; cᶜ-lower-right = id★
    ; cᶜ-comparable = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ ★ ★ D →
      Φᴼ ⊢ ★ ⊑ D →
      Φᴼ ⊢ D ⊑ ★
    comparable {D = ★} common id★ = id★

maximal-star-starᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ ★
maximal-star-starᶜ = comparable⇒maximalᶜ comparable-star-starᶜ

comparable-base-baseᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  ComparableMaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (‵ ι) (‵ ι)
comparable-base-baseᶜ =
  record
    { cᶜ-lower = ‵ _
    ; cᶜ-lower-left = idι
    ; cᶜ-lower-right = idι
    ; cᶜ-comparable = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ ι D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ (‵ ι) (‵ ι) D →
      Φᴼ ⊢ ‵ ι ⊑ D →
      Φᴼ ⊢ D ⊑ ‵ ι
    comparable common idι = idι
    comparable (() , _) (tag ι)

maximal-base-baseᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (‵ ι) (‵ ι)
maximal-base-baseᶜ = comparable⇒maximalᶜ comparable-base-baseᶜ

comparable-base-starᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  ComparableMaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (‵ ι) ★
comparable-base-starᶜ =
  record
    { cᶜ-lower = ‵ _
    ; cᶜ-lower-left = idι
    ; cᶜ-lower-right = tag _
    ; cᶜ-comparable = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ ι D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ (‵ ι) ★ D →
      Φᴼ ⊢ ‵ ι ⊑ D →
      Φᴼ ⊢ D ⊑ ‵ ι
    comparable common idι = idι
    comparable (() , _) (tag ι)

maximal-base-starᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (‵ ι) ★
maximal-base-starᶜ = comparable⇒maximalᶜ comparable-base-starᶜ

comparable-star-baseᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  ComparableMaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ (‵ ι)
comparable-star-baseᶜ =
  record
    { cᶜ-lower = ‵ _
    ; cᶜ-lower-left = tag _
    ; cᶜ-lower-right = idι
    ; cᶜ-comparable = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ ι D} →
      CommonLowerBoundᶜ Φᴸ Φᴿ ★ (‵ ι) D →
      Φᴼ ⊢ ‵ ι ⊑ D →
      Φᴼ ⊢ D ⊑ ‵ ι
    comparable common idι = idι
    comparable (_ , ()) (tag ι)

maximal-star-baseᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ (‵ ι)
maximal-star-baseᶜ = comparable⇒maximalᶜ comparable-star-baseᶜ

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

⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-ˣ∈ {Φ = []} ()
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)

⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-★∈ {Φ = []} ()
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)

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

un⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸᵢ-ˣ∈ {Φ = []} ()
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-ˣ∈ x∈)
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-ˣ∈ x∈)

un⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸᵢ-★∈ {Φ = []} ()
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)

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

no-⇑ᴸᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-star {Φ = []} ()
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈

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

idᵢ-var-refl-right :
  ∀ {Δ W X} →
  (W ˣ⊑ˣ X) ∈ idᵢ Δ →
  (X ˣ⊑ˣ X) ∈ idᵢ Δ
idᵢ-var-refl-right {Δ = Δ} w⊑x =
  idᵢ-refl-∈
    (subst (λ Z → Z < Δ) (idᵢ-var-identity w⊑x)
      (idᵢ-var-left-bound w⊑x))

idᵢ-var-rewrite-left :
  ∀ {Δ W X Y} →
  (W ˣ⊑ˣ X) ∈ idᵢ Δ →
  (W ˣ⊑ˣ Y) ∈ idᵢ Δ →
  (X ˣ⊑ˣ Y) ∈ idᵢ Δ
idᵢ-var-rewrite-left {Δ = Δ} {Y = Y} w⊑x w⊑y =
  subst (λ Z → (Z ˣ⊑ˣ Y) ∈ idᵢ Δ) (idᵢ-var-identity w⊑x) w⊑y

------------------------------------------------------------------------
-- Variable lower-bound selectors
------------------------------------------------------------------------

record MlbVarCtx (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    mlb-var-var :
      ∀ {W X Y} →
      (W ˣ⊑ˣ X) ∈ Φᴸ →
      (W ˣ⊑ˣ Y) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

    mlb-var-star :
      ∀ {W X} →
      (W ˣ⊑ˣ X) ∈ Φᴸ →
      (W ˣ⊑★) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑★) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

    mlb-star-var :
      ∀ {W Y} →
      (W ˣ⊑★) ∈ Φᴸ →
      (W ˣ⊑ˣ Y) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑★) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

open MlbVarCtx public

MlbVarCtx-idᵢ : ∀ Δ → MlbVarCtx (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
MlbVarCtx-idᵢ Δ .mlb-var-var {X = X} w⊑x w⊑y =
  X , idᵢ-var-refl-right w⊑x , idᵢ-var-rewrite-left w⊑x w⊑y ,
  λ w′⊑x w′⊑y → w′⊑x
MlbVarCtx-idᵢ Δ .mlb-var-star w⊑x w⊑★ =
  ⊥-elim (idᵢ-no-star w⊑★)
MlbVarCtx-idᵢ Δ .mlb-star-var w⊑★ w⊑y =
  ⊥-elim (idᵢ-no-star w⊑★)

MlbVarCtx-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  MlbVarCtx ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
MlbVarCtx-∀∀ V .mlb-var-var (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
    greatest :
      ∀ {W} →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _) →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _) →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
    greatest (here refl) (here refl) = here refl
    greatest (here refl) (there w⊑0) =
      ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
    greatest (there w⊑0) _ =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ V .mlb-var-var (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
MlbVarCtx-∀∀ V .mlb-var-var (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ V .mlb-var-var {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ V .mlb-var-var {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ V .mlb-var-var {W = suc W} {Y = zero}
    p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-var {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ X) ∈ Φᴸ →
            (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-var V (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ suc X) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑ˣ suc Y) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-ˣ∈ w′⊑x)
            (un⇑ᵢ-ˣ∈ w′⊑y)))
MlbVarCtx-∀∀ V .mlb-var-star (here refl) (here ())
MlbVarCtx-∀∀ V .mlb-var-star (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ V .mlb-var-star {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ V .mlb-var-star {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-star {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ X) ∈ Φᴸ →
            (W′ ˣ⊑★) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-star V (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ suc X) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑★) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-ˣ∈ w′⊑x)
            (un⇑ᵢ-★∈ w′⊑★)))
MlbVarCtx-∀∀ V .mlb-star-var (here ()) q
MlbVarCtx-∀∀ V .mlb-star-var (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ V .mlb-star-var {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ V .mlb-star-var {W = suc W} {Y = zero}
    p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-star-var {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑★) ∈ Φᴸ →
            (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-star-var V (un⇑ᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑ˣ suc Y) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑★) q =
      ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
    greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-★∈ w′⊑★)
            (un⇑ᵢ-ˣ∈ w′⊑y)))

MlbVarCtx-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  MlbVarCtx ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ)
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
MlbVarCtx-∀ν V .mlb-var-var (here refl) (here ())
MlbVarCtx-∀ν V .mlb-var-var (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
MlbVarCtx-∀ν V .mlb-var-var {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀ν V .mlb-var-var {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-var {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ _) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ X) ∈ Φᴸ →
            (W′ ˣ⊑ˣ _) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-var V (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ suc X) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑ˣ _) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-ˣ∈ w′⊑x)
            (un⇑ᴸᵢ-ˣ∈ w′⊑y)))
MlbVarCtx-∀ν V .mlb-var-star (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
    greatest :
      ∀ {W} →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _) →
      (W ˣ⊑★) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ _) →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
    greatest (here refl) (here refl) = here refl
    greatest (here refl) (there w⊑★) =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
    greatest (there w⊑0) q =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀ν V .mlb-var-star (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-∀ν V .mlb-var-star {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀ν V .mlb-var-star {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-star {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ X) ∈ Φᴸ →
            (W′ ˣ⊑★) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-star V (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ suc X) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑★) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-ˣ∈ w′⊑x)
            (un⇑ᴸᵢ-★∈ w′⊑★)))
MlbVarCtx-∀ν V .mlb-star-var (here ()) q
MlbVarCtx-∀ν V .mlb-star-var p (here ())
MlbVarCtx-∀ν V .mlb-star-var {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-star-var {W = suc W} (there w⊑★) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ _) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑★) ∈ Φᴸ →
            (W′ ˣ⊑ˣ _) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-star-var V (un⇑ᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴸ) →
      (W′ ˣ⊑ˣ _) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑★) q =
      ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
    greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᵢ-★∈ w′⊑★)
            (un⇑ᴸᵢ-ˣ∈ w′⊑y)))

MlbVarCtx-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  MlbVarCtx ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
MlbVarCtx-ν∀ V .mlb-var-var (here ()) q
MlbVarCtx-ν∀ V .mlb-var-var (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ V .mlb-var-var {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ V .mlb-var-var {W = suc W} {Y = zero}
    p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-var {W = suc W} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ _) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ _) ∈ Φᴸ →
            (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-var V (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ _) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ) →
      (W′ ˣ⊑ˣ suc Y) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᴸᵢ-ˣ∈ w′⊑x)
            (un⇑ᵢ-ˣ∈ w′⊑y)))
MlbVarCtx-ν∀ V .mlb-var-star (here ()) q
MlbVarCtx-ν∀ V .mlb-var-star p (here ())
MlbVarCtx-ν∀ V .mlb-var-star {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-var-star {W = suc W} (there w⊑x) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑ˣ _) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑ˣ _) ∈ Φᴸ →
            (W′ ˣ⊑★) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-var-star V (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑ˣ _) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ) →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (there w′⊑x) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′} (there w′⊑x) (there w′⊑★) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᴸᵢ-ˣ∈ w′⊑x)
            (un⇑ᵢ-★∈ w′⊑★)))
MlbVarCtx-ν∀ V .mlb-star-var (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
    greatest :
      ∀ {W} →
      (W ˣ⊑★) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ _) →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _) →
      (W ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
    greatest (here refl) (here refl) = here refl
    greatest (here refl) (there w⊑0) =
      ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
    greatest {W = zero} (there w⊑★) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
    greatest {W = suc W} p (there w⊑0) =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ V .mlb-star-var (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
MlbVarCtx-ν∀ V .mlb-star-var (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-ν∀ V .mlb-star-var {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-ν∀ V .mlb-star-var {W = suc W} {Y = zero}
    p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} V
    .mlb-star-var {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
    r : Σ[ Z ∈ TyVar ]
          ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
           (∀ {W′} →
            (W′ ˣ⊑★) ∈ Φᴸ →
            (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
            (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
    r = mlb-star-var V (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y)

    greatest′ :
      ∀ {W′} →
      (W′ ˣ⊑★) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ) →
      (W′ ˣ⊑ˣ suc Y) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ) →
      (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
    greatest′ {W′ = zero} (here refl) (there w′⊑y) =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑y)
    greatest′ {W′ = zero} (there w′⊑★) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w′⊑★)
    greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑y) =
      there
        (⇑ᵢ-ˣ∈
          (proj₂ (proj₂ (proj₂ r))
            (un⇑ᴸᵢ-★∈ w′⊑★)
            (un⇑ᵢ-ˣ∈ w′⊑y)))

no-νν-id1-one-one :
  (suc zero ˣ⊑ˣ suc zero) ∈
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ (suc zero))) →
  ⊥
no-νν-id1-one-one (here ())
no-νν-id1-one-one (there (here ()))
no-νν-id1-one-one (there (there ()))

no-νν-id1-sucsuc-zero :
  ∀ {Z} →
  (suc (suc Z) ˣ⊑ˣ zero) ∈
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ (suc zero))) →
  ⊥
no-νν-id1-sucsuc-zero (here ())
no-νν-id1-sucsuc-zero (there (here ()))
no-νν-id1-sucsuc-zero (there (there ()))

no-MlbVarCtx-νν-id1 :
  ¬ MlbVarCtx
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ (suc zero)))
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ (suc zero)))
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ (suc zero)))
no-MlbVarCtx-νν-id1 V
    with mlb-var-var V (there (here refl)) (there (here refl))
no-MlbVarCtx-νν-id1 V | zero , z⊑0 , z⊑0′ , greatest =
  no-νctx-zero-var z⊑0
no-MlbVarCtx-νν-id1 V | suc zero , z⊑0 , z⊑0′ , greatest =
  no-νν-id1-one-one (greatest (there (here refl)) (there (here refl)))
no-MlbVarCtx-νν-id1 V | suc (suc z) , z⊑0 , z⊑0′ , greatest =
  no-νν-id1-sucsuc-zero z⊑0

------------------------------------------------------------------------
-- Mode contexts for computing candidate lower-bound types
------------------------------------------------------------------------

data MlbMode : Set where
  same : MlbMode
  left : MlbMode
  right : MlbMode
  neither : MlbMode

MlbChoiceCtx : Set
MlbChoiceCtx = List MlbMode

leftChoice : MlbChoiceCtx → ImpCtx
leftChoice [] = []
leftChoice (same ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (leftChoice Γ)
leftChoice (left ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (leftChoice Γ)
leftChoice (right ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (leftChoice Γ)
leftChoice (neither ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (leftChoice Γ)

rightChoice : MlbChoiceCtx → ImpCtx
rightChoice [] = []
rightChoice (same ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (rightChoice Γ)
rightChoice (left ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (rightChoice Γ)
rightChoice (right ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (rightChoice Γ)
rightChoice (neither ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (rightChoice Γ)

choice-id : TyCtx → MlbChoiceCtx
choice-id zero = []
choice-id (suc Δ) = same ∷ choice-id Δ

leftChoice-id : ∀ Δ → leftChoice (choice-id Δ) ≡ idᵢ Δ
leftChoice-id zero = refl
leftChoice-id (suc Δ) = cong (λ Φ → (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
                              (leftChoice-id Δ)

rightChoice-id : ∀ Δ → rightChoice (choice-id Δ) ≡ idᵢ Δ
rightChoice-id zero = refl
rightChoice-id (suc Δ) = cong (λ Φ → (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
                               (rightChoice-id Δ)

choice-var-var :
  ∀ Γ {W X Y} →
  (W ˣ⊑ˣ X) ∈ leftChoice Γ →
  (W ˣ⊑ˣ Y) ∈ rightChoice Γ →
  TyVar
choice-var-var [] ()
choice-var-var (same ∷ Γ) (here refl) (here refl) = zero
choice-var-var (same ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-var-var (same ∷ Γ) (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var (same ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var (same ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-var (same ∷ Γ) {W = suc W} {Y = zero} p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-var (same ∷ Γ) {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-var Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y))
choice-var-var (left ∷ Γ) (here refl) (here ())
choice-var-var (left ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-var-var (left ∷ Γ) (there w⊑x) (here ())
choice-var-var (left ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var (left ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-var (left ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-var Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y))
choice-var-var (right ∷ Γ) (here ()) q
choice-var-var (right ∷ Γ) (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var (right ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var (right ∷ Γ) {W = suc W} {Y = zero} p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-var (right ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-var Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y))
choice-var-var (neither ∷ Γ) (here ()) q
choice-var-var (neither ∷ Γ) p (here ())
choice-var-var (neither ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var (neither ∷ Γ) {W = suc W} (there w⊑x) (there w⊑y) =
  suc (choice-var-var Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y))

choice-var-star :
  ∀ Γ {W X} →
  (W ˣ⊑ˣ X) ∈ leftChoice Γ →
  (W ˣ⊑★) ∈ rightChoice Γ →
  TyVar
choice-var-star [] ()
choice-var-star (same ∷ Γ) (here refl) (here ())
choice-var-star (same ∷ Γ) (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-var-star (same ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star (same ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-star (same ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (choice-var-star Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★))
choice-var-star (left ∷ Γ) (here refl) (here refl) = zero
choice-var-star (left ∷ Γ) (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-var-star (left ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star (left ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-star (left ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (choice-var-star Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★))
choice-var-star (right ∷ Γ) (here ()) q
choice-var-star (right ∷ Γ) p (here ())
choice-var-star (right ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star (right ∷ Γ) {W = suc W} (there w⊑x) (there w⊑★) =
  suc (choice-var-star Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★))
choice-var-star (neither ∷ Γ) (here ()) q
choice-var-star (neither ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star (neither ∷ Γ) {W = suc W} (there w⊑x) (there w⊑★) =
  suc (choice-var-star Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★))

choice-star-var :
  ∀ Γ {W Y} →
  (W ˣ⊑★) ∈ leftChoice Γ →
  (W ˣ⊑ˣ Y) ∈ rightChoice Γ →
  TyVar
choice-star-var [] ()
choice-star-var (same ∷ Γ) (here ()) q
choice-star-var (same ∷ Γ) (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var (same ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var (same ∷ Γ) {W = suc W} {Y = zero} p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-star-var (same ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (choice-star-var Γ (un⇑ᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y))
choice-star-var (left ∷ Γ) (here ()) q
choice-star-var (left ∷ Γ) p (here ())
choice-star-var (left ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var (left ∷ Γ) {W = suc W} (there w⊑★) (there w⊑y) =
  suc (choice-star-var Γ (un⇑ᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y))
choice-star-var (right ∷ Γ) (here refl) (here refl) = zero
choice-star-var (right ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-star-var (right ∷ Γ) (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var (right ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var (right ∷ Γ) {W = suc W} {Y = zero} p (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-star-var (right ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (choice-star-var Γ (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y))
choice-star-var (neither ∷ Γ) p (here ())
choice-star-var (neither ∷ Γ) {W = zero} (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-star-var (neither ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var (neither ∷ Γ) {W = suc W} (there w⊑★) (there w⊑y) =
  suc (choice-star-var Γ (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y))

close-neither : Ty → Ty
close-neither A with occurs zero A
close-neither A | true = `∀ A
close-neither A | false = A [ zero ]ᴿ

split-∀ : Ty → ℕ × (∃[ A ] Non∀ A)
split-∀ (＇ X) = 0 , ＇ X , non∀-＇
split-∀ (‵ ι) = 0 , ‵ ι , non∀-‵
split-∀ ★ = 0 , ★ , non∀-★
split-∀ (A ⇒ B) = 0 , A ⇒ B , non∀-⇒
split-∀ (`∀ A)
    with split-∀ A
... | n , B , n∀ = suc n , B , n∀

clash? : (TyVar × TyVar) → (TyVar × TyVar) → Bool
clash? (X , Y) (X′ , Y′) with X ≟ X′ | Y ≟ Y′
clash? (X , Y) (X′ , Y′) | yes _ | yes _ = false
clash? (X , Y) (X′ , Y′) | yes _ | no _ = true
clash? (X , Y) (X′ , Y′) | no _ | yes _ = true
clash? (X , Y) (X′ , Y′) | no _ | no _ = false

same-eqn? : (TyVar × TyVar) → (TyVar × TyVar) → Bool
same-eqn? (X , Y) (X′ , Y′) with X ≟ X′ | Y ≟ Y′
same-eqn? (X , Y) (X′ , Y′) | yes _ | yes _ = true
same-eqn? (X , Y) (X′ , Y′) | yes _ | no _ = false
same-eqn? (X , Y) (X′ , Y′) | no _ | yes _ = false
same-eqn? (X , Y) (X′ , Y′) | no _ | no _ = false

insert-eqn : (TyVar × TyVar) → List (TyVar × TyVar)
  → Maybe (List (TyVar × TyVar))
insert-eqn eq [] = just (eq ∷ [])
insert-eqn eq₁ (eq₂ ∷ eqs′)
    with same-eqn? eq₁ eq₂ | clash? eq₁ eq₂
... | true | _ = just (eq₂ ∷ eqs′)
... | false | true = nothing
... | false | false
    with insert-eqn eq₁ eqs′
... | nothing = nothing
... | just eqs = just (eq₂ ∷ eqs)

merge-eqns : List (TyVar × TyVar) → List (TyVar × TyVar)
  → Maybe (List (TyVar × TyVar))
merge-eqns [] eqs′ = just eqs′
merge-eqns (eq ∷ eqs) eqs′
    with merge-eqns eqs eqs′
... | nothing = nothing
... | just eqs″ = insert-eqn eq eqs″ 

add∀ : ℕ → Ty → Ty
add∀ zero A = A
add∀ (suc n) A = `∀ (add∀ n A)

rename-non∀ : ∀ {ρ A} → Non∀ A → Non∀ (renameᵗ ρ A)
rename-non∀ non∀-＇ = non∀-＇
rename-non∀ non∀-‵ = non∀-‵
rename-non∀ non∀-★ = non∀-★
rename-non∀ non∀-⇒ = non∀-⇒

embed-left-var : ℕ → ℕ → TyVar → TyVar
embed-left-var n m X with X <? n
... | yes _ = X
... | no _ = n + m + (X ∸ n)

embed-right-var : ℕ → ℕ → TyVar → TyVar
embed-right-var n m Y with Y <? m
... | yes _ = n + Y
... | no _ = n + m + (Y ∸ m)

right-bound? : ℕ → ℕ → TyVar → Bool
right-bound? n m Y with Y <? n | Y <? (n + m)
... | yes _ | _ = false
... | no _ | yes _ = true
... | no _ | no _ = false

bound-eqn? : ℕ → ℕ → (TyVar × TyVar) → Bool
bound-eqn? n m (X , Y) with X <? n | right-bound? n m Y
... | yes _ | true = true
... | yes _ | false = false
... | no _ | _ = false

bound-eqn-count : ℕ → ℕ → List (TyVar × TyVar) → ℕ
bound-eqn-count n m [] = zero
bound-eqn-count n m (eq ∷ eqs) with bound-eqn? n m eq
... | true = suc (bound-eqn-count n m eqs)
... | false = bound-eqn-count n m eqs

mlb-∀-count : ℕ → ℕ → List (TyVar × TyVar) → ℕ
mlb-∀-count n m eqs = (n + m) ∸ bound-eqn-count n m eqs

find-left-for-right : TyVar → List (TyVar × TyVar) → Maybe TyVar
find-left-for-right Y [] = nothing
find-left-for-right Y ((X , Y′) ∷ eqs) with Y ≟ Y′
... | yes _ = just X
... | no _ = find-left-for-right Y eqs

matched-right? : TyVar → List (TyVar × TyVar) → Bool
matched-right? Y [] = false
matched-right? Y ((X , Y′) ∷ eqs) with Y ≟ Y′
... | yes _ = true
... | no _ = matched-right? Y eqs

unmatched-right-before : ℕ → ℕ → List (TyVar × TyVar) → ℕ
unmatched-right-before n zero eqs = zero
unmatched-right-before n (suc Y) eqs
    with matched-right? (n + Y) eqs
... | true = unmatched-right-before n Y eqs
... | false = suc (unmatched-right-before n Y eqs)

normalize-var : ℕ → ℕ → List (TyVar × TyVar) → TyVar → TyVar
normalize-var n m eqs X with X <? n | X <? (n + m)
... | yes _ | _ = X
... | no _ | yes _
    with find-left-for-right X eqs
... | just Y = Y
... | nothing = n + unmatched-right-before n (X ∸ n) eqs
normalize-var n m eqs X | no _ | no _ =
  mlb-∀-count n m eqs + (X ∸ (n + m))

normalize-eqns :
  ℕ → ℕ → List (TyVar × TyVar) → Maybe (List (TyVar × TyVar))
normalize-eqns n m [] = just []
normalize-eqns n m ((X , Y) ∷ eqs)
    with normalize-eqns n m eqs | bound-eqn? n m (X , Y)
... | nothing | _ = nothing
... | just eqs′ | true = just eqs′
... | just eqs′ | false =
  insert-eqn (normalize-var n m ((X , Y) ∷ eqs) X ,
              normalize-var n m ((X , Y) ∷ eqs) Y)
             eqs′

mutual
  {-# TERMINATING #-}
  search-mlb? : (A B : Ty) → Maybe (Ty × List (TyVar × TyVar))
  search-mlb? A B
      with split-∀ A | split-∀ B
  ... | n , A′ , n∀A′ | m , B′ , n∀B′
      with core-mlb?
             (renameᵗ (embed-left-var n m) A′)
             (renameᵗ (embed-right-var n m) B′)
             (rename-non∀ n∀A′)
             (rename-non∀ n∀B′)
  ... | nothing = nothing
  ... | just (C , Eq)
      with normalize-eqns n m Eq
  ... | nothing = nothing
  ... | just Eq′ =
    just ( add∀ (mlb-∀-count n m Eq) (renameᵗ (normalize-var n m Eq) C)
         , Eq′
         )

  core-mlb? : (A B : Ty) → Non∀ A → Non∀ B → Maybe (Ty × List (TyVar × TyVar))
  core-mlb? (＇ X) (＇ Y) n∀A n∀B = just ((＇ X) , (X , Y) ∷ [])
  core-mlb? (＇ X) (‵ ι) n∀A n∀B = nothing
  core-mlb? (＇ X) ★ n∀A n∀B = just ((＇ X) , [])
  core-mlb? (＇ X) (B₁ ⇒ B₂) n∀A n∀B = nothing
  core-mlb? (‵ ι) (＇ x) n∀A n∀B = nothing
  core-mlb? (‵ ι₁) (‵ ι₂) n∀A n∀B
      with ι₁ ≟Base ι₂
  ... | yes refl = just (‵ ι₁ , [])
  ... | no neq = nothing
  core-mlb? (‵ ι) ★ n∀A n∀B = just ((‵ ι) , [])
  core-mlb? (‵ ι) (B₁ ⇒ B₂) n∀A n∀B = nothing
  core-mlb? ★ B n∀A n∀B = just (B , [])
  core-mlb? (A₁ ⇒ A₂) (＇ X) n∀A n∀B = nothing
  core-mlb? (A₁ ⇒ A₂) (‵ ι) n∀A n∀B = nothing
  core-mlb? (A₁ ⇒ A₂) ★ n∀A n∀B = just (A₁ ⇒ A₂ , [])
  core-mlb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) n∀A n∀B
      with search-mlb? A₁ B₁ | search-mlb? A₂ B₂
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just (C₁ , Eq₁) | just (C₂ , Eq₂)
      with merge-eqns Eq₁ Eq₂
  ... | nothing = nothing
  ... | just Eq = just (C₁ ⇒ C₂ , Eq)
  core-mlb? (A₁ ⇒ A₂) (`∀ B) n∀A ()


mlb? : (A B : Ty) → Maybe Ty
mlb? A B with search-mlb? A B
... | nothing = nothing
... | just (C , Eq) = just C

mlb-type :
  ∀ {Γ A B C} →
  leftChoice Γ ⊢ C ⊑ A →
  rightChoice Γ ⊢ C ⊑ B →
  Ty
mlb-type {Γ = Γ} id★ id★ = ★
mlb-type {Γ = Γ} (idˣ w⊑x) (idˣ w⊑y) =
  ＇ choice-var-var Γ w⊑x w⊑y
mlb-type {Γ = Γ} (idι {ι = ι}) idι = ‵ ι
mlb-type {Γ = Γ} idι (tag ι) = ‵ ι
mlb-type {Γ = Γ} (p₁ ↦ p₂) (q₁ ↦ q₂) =
  mlb-type p₁ q₁ ⇒ mlb-type p₂ q₂
mlb-type {Γ = Γ} (p₁ ↦ p₂) (tag_⇒_ q₁ q₂) =
  mlb-type p₁ q₁ ⇒ mlb-type p₂ q₂
mlb-type {Γ = Γ} (∀ⁱ p) (∀ⁱ q) =
  `∀ (mlb-type {Γ = same ∷ Γ} p q)
mlb-type {Γ = Γ} (∀ⁱ p) (ν occ q) =
  `∀ (mlb-type {Γ = left ∷ Γ} p q)
mlb-type {Γ = Γ} (tag ι) idι = ‵ ι
mlb-type {Γ = Γ} (tag ι) (tag .ι) = ★
mlb-type {Γ = Γ} (tag_⇒_ p₁ p₂) (q₁ ↦ q₂) =
  mlb-type p₁ q₁ ⇒ mlb-type p₂ q₂
mlb-type {Γ = Γ} (tag_⇒_ p₁ p₂) (tag_⇒_ q₁ q₂) = ★
mlb-type {Γ = Γ} (tagˣ w⊑★) (idˣ w⊑y) =
  ＇ choice-star-var Γ w⊑★ w⊑y
mlb-type {Γ = Γ} (tagˣ w⊑★) (tagˣ w⊑★′) = ★
mlb-type {Γ = Γ} (ν occ p) (∀ⁱ q) =
  `∀ (mlb-type {Γ = right ∷ Γ} p q)
mlb-type {Γ = Γ} (ν occ p) (ν occ′ q) =
  close-neither (mlb-type {Γ = neither ∷ Γ} p q)
mlb-type {Γ = Γ} (idˣ w⊑x) (tagˣ w⊑★) =
  ＇ choice-var-star Γ w⊑x w⊑★

mlb-type-from-lower :
  ∀ {Δ A B C} →
  idᵢ Δ ⊢ C ⊑ A →
  idᵢ Δ ⊢ C ⊑ B →
  Ty
mlb-type-from-lower {Δ = Δ} C⊑A C⊑B =
  mlb-type {Γ = choice-id Δ}
    (subst (λ Φ → Φ ⊢ _ ⊑ _) (sym (leftChoice-id Δ)) C⊑A)
    (subst (λ Φ → Φ ⊢ _ ⊑ _) (sym (rightChoice-id Δ)) C⊑B)

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

maximal-id-var-varᶜ :
  ∀ {Δ X Y Z} →
  (X ˣ⊑ˣ Y) ∈ idᵢ Δ →
  (X ˣ⊑ˣ Z) ∈ idᵢ Δ →
  MaximalLowerBoundᶜ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) (＇ Y) (＇ Z)
maximal-id-var-varᶜ x⊑y x⊑z
    rewrite sym (idᵢ-var-identity x⊑y)
          | sym (idᵢ-var-identity x⊑z) =
  maximal-idᶜ (maximal-var-var (idᵢ-var-left-bound x⊑y))

maximal-var-varᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ W X Y} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (＇ X) (＇ Y)
maximal-var-varᶜ V w⊑x w⊑y =
  record
    { lowerᶜ = ＇ proj₁ selected
    ; lower-leftᶜ = idˣ (proj₁ (proj₂ selected))
    ; lower-rightᶜ = idˣ (proj₁ (proj₂ (proj₂ selected)))
    ; maximalᶜ = maximal′
    }
  where
    selected =
      mlb-var-var V w⊑x w⊑y

    greatest =
      proj₂ (proj₂ (proj₂ selected))

    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ (＇ _) (＇ _) D →
      ¬ StrictlyBelowᶜ _ (＇ proj₁ selected) D
    maximal′ ((idˣ d⊑x) , (idˣ d⊑y))
        ((idˣ z⊑d) , ¬D⊑Z) =
      ¬D⊑Z (idˣ (greatest d⊑x d⊑y))

maximal-var-starᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ W X} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑★) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (＇ X) ★
maximal-var-starᶜ V w⊑x w⊑★ =
  record
    { lowerᶜ = ＇ proj₁ selected
    ; lower-leftᶜ = idˣ (proj₁ (proj₂ selected))
    ; lower-rightᶜ = tagˣ (proj₁ (proj₂ (proj₂ selected)))
    ; maximalᶜ = maximal′
    }
  where
    selected =
      mlb-var-star V w⊑x w⊑★

    greatest =
      proj₂ (proj₂ (proj₂ selected))

    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ (＇ _) ★ D →
      ¬ StrictlyBelowᶜ _ (＇ proj₁ selected) D
    maximal′ ((idˣ d⊑x) , (tagˣ d⊑★))
        ((idˣ z⊑d) , ¬D⊑Z) =
      ¬D⊑Z (idˣ (greatest d⊑x d⊑★))

maximal-star-varᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ W Y} →
  MlbVarCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑★) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ (＇ Y)
maximal-star-varᶜ V w⊑★ w⊑y =
  record
    { lowerᶜ = ＇ proj₁ selected
    ; lower-leftᶜ = tagˣ (proj₁ (proj₂ selected))
    ; lower-rightᶜ = idˣ (proj₁ (proj₂ (proj₂ selected)))
    ; maximalᶜ = maximal′
    }
  where
    selected =
      mlb-star-var V w⊑★ w⊑y

    greatest =
      proj₂ (proj₂ (proj₂ selected))

    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ ★ (＇ _) D →
      ¬ StrictlyBelowᶜ _ (＇ proj₁ selected) D
    maximal′ ((tagˣ d⊑★) , (idˣ d⊑y))
        ((idˣ z⊑d) , ¬D⊑Z) =
      ¬D⊑Z (idˣ (greatest d⊑★ d⊑y))
    maximal′ (_ , ()) ((tagˣ z⊑★) , ¬D⊑Z)

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

maximal-arrow-arrow :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBound Δ A₁ B₁ →
  ComparableMaximalLowerBound Δ A₂ B₂ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow c₁ c₂ =
  comparable⇒maximal (comparable-arrow-arrow c₁ c₂)

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

maximal-arrow-arrow-from-maximalᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ A₂ B₁ B₂} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₁ B₁ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₂ B₂ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow-from-maximalᶜ mlb₁ mlb₂ =
  record
    { lowerᶜ = lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂
    ; lower-leftᶜ = lower-leftᶜ mlb₁ ↦ lower-leftᶜ mlb₂
    ; lower-rightᶜ = lower-rightᶜ mlb₁ ↦ lower-rightᶜ mlb₂
    ; maximalᶜ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ (_ ⇒ _) (_ ⇒ _) D →
      ¬ StrictlyBelowᶜ _ (lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜ mlb₁ (D₁⊑A₁ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜ mlb₂ (D₂⊑A₂ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

maximal-star-arrow-from-maximalᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ B₁ B₂} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ B₁ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ B₂ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ (B₁ ⇒ B₂)
maximal-star-arrow-from-maximalᶜ mlb₁ mlb₂ =
  record
    { lowerᶜ = lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂
    ; lower-leftᶜ = tag_⇒_ (lower-leftᶜ mlb₁) (lower-leftᶜ mlb₂)
    ; lower-rightᶜ = lower-rightᶜ mlb₁ ↦ lower-rightᶜ mlb₂
    ; maximalᶜ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelowᶜ _ (lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂) D
    maximal′ ((tag_⇒_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜ mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜ mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇒_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximalᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ A₂} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₁ ★ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₂ ★ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximalᶜ mlb₁ mlb₂ =
  record
    { lowerᶜ = lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂
    ; lower-leftᶜ = lower-leftᶜ mlb₁ ↦ lower-leftᶜ mlb₂
    ; lower-rightᶜ = tag_⇒_ (lower-rightᶜ mlb₁) (lower-rightᶜ mlb₂)
    ; maximalᶜ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelowᶜ _ (lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇒_ D₁⊑★ D₂⊑★))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜ mlb₁ (D₁⊑A₁ , D₁⊑★)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜ mlb₂ (D₂⊑A₂ , D₂⊑★)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

------------------------------------------------------------------------
-- Binder lifting support
------------------------------------------------------------------------

data ForallForallLower²ᶜ
    (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Set where
  ff-via-∀∀ :
    ∀ {A B C}
      {occC : occurs zero C ≡ true}
      {occA : occurs zero A ≡ true}
      {occB : occurs zero B ≡ true} →
    liftCtx ∀ᵇ Φᴸ ⊢ C ⊑ A →
    liftCtx ∀ᵇ Φᴿ ⊢ C ⊑ B →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

  ff-via-∀ν :
    ∀ {A B C}
      {occC : occurs zero C ≡ true}
      {occA : occurs zero A ≡ true} →
    liftCtx ∀ᵇ Φᴸ ⊢ C ⊑ A →
    liftCtx νᵇ Φᴿ ⊢ C ⊑ ⇑ᵗ (`∀ B) →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

  ff-via-ν∀ :
    ∀ {A B C}
      {occC : occurs zero C ≡ true}
      {occB : occurs zero B ≡ true} →
    liftCtx νᵇ Φᴸ ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    liftCtx ∀ᵇ Φᴿ ⊢ C ⊑ B →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

  ff-via-νν :
    ∀ {A B C} →
    occurs zero C ≡ true →
    liftCtx νᵇ Φᴸ ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    liftCtx νᵇ Φᴿ ⊢ C ⊑ ⇑ᵗ (`∀ B) →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

forall-forall-lower²-invᶜ :
  ∀ {Φᴸ Φᴿ A B C} →
  Φᴸ ⊢ C ⊑ `∀ A →
  Φᴿ ⊢ C ⊑ `∀ B →
  ForallForallLower²ᶜ Φᴸ Φᴿ C A B
forall-forall-lower²-invᶜ
    (∀ⁱ_ {occA = occC} {occB = occA} C⊑A)
    (∀ⁱ_ {occB = occB} C⊑B) =
  ff-via-∀∀ {occC = occC} {occA = occA} {occB = occB} C⊑A C⊑B
forall-forall-lower²-invᶜ
    (∀ⁱ_ {occA = occC} {occB = occA} C⊑A)
    (ν occC′ C⊑∀B) =
  ff-via-∀ν {occC = occC} {occA = occA} C⊑A C⊑∀B
forall-forall-lower²-invᶜ
    (ν occC C⊑∀A)
    (∀ⁱ_ {occB = occB} C⊑B) =
  ff-via-ν∀ {occC = occC} {occB = occB} C⊑∀A C⊑B
forall-forall-lower²-invᶜ (ν occC C⊑∀A) (ν occC′ C⊑∀B) =
  ff-via-νν occC C⊑∀A C⊑∀B

record LiftMlb∀∀Support
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B C : Ty) : Set where
  field
    k∀ν :
      ∀ {D} →
      liftCtx ∀ᵇ Φᴸ ⊢ D ⊑ A →
      occurs zero D ≡ true →
      occurs zero A ≡ true →
      liftCtx νᵇ Φᴿ ⊢ D ⊑ ⇑ᵗ (`∀ B) →
      Φᴼ ⊢ `∀ D ⊑ `∀ C

    kν∀ :
      ∀ {D} →
      occurs zero D ≡ true →
      liftCtx νᵇ Φᴸ ⊢ D ⊑ ⇑ᵗ (`∀ A) →
      liftCtx ∀ᵇ Φᴿ ⊢ D ⊑ B →
      occurs zero B ≡ true →
      Φᴼ ⊢ `∀ D ⊑ `∀ C

    kνν :
      ∀ {D} →
      occurs zero D ≡ true →
      liftCtx νᵇ Φᴸ ⊢ D ⊑ ⇑ᵗ (`∀ A) →
      liftCtx νᵇ Φᴿ ⊢ D ⊑ ⇑ᵗ (`∀ B) →
      Φᴼ ⊢ `∀ D ⊑ `∀ C

open LiftMlb∀∀Support public

left-∀∀-support :
  ∀ {Φᴸ Φᴿ A B} →
  LiftMlb∀∀Support Φᴸ Φᴿ Φᴸ A B A
left-∀∀-support .k∀ν D⊑A occD occA D⊑∀B =
  ∀ⁱ_ {occA = occD} {occB = occA} D⊑A
left-∀∀-support .kν∀ occD D⊑∀A D⊑B occB = ν occD D⊑∀A
left-∀∀-support .kνν occD D⊑∀A D⊑∀B = ν occD D⊑∀A

right-∀∀-support :
  ∀ {Φᴸ Φᴿ A B} →
  LiftMlb∀∀Support Φᴸ Φᴿ Φᴿ A B B
right-∀∀-support .k∀ν D⊑A occD occA D⊑∀B = ν occD D⊑∀B
right-∀∀-support .kν∀ occD D⊑∀A D⊑B occB =
  ∀ⁱ_ {occA = occD} {occB = occB} D⊑B
right-∀∀-support .kνν occD D⊑∀A D⊑∀B = ν occD D⊑∀B

forall-forall-support-dispatch :
  ∀ {Φᴸ Φᴿ Φᴼ A B C D} →
  LiftMlb∀∀Support Φᴸ Φᴿ Φᴼ A B C →
  ForallForallLower²ᶜ Φᴸ Φᴿ D A B →
  (∀ {E} →
   liftCtx ∀ᵇ Φᴸ ⊢ E ⊑ A →
   liftCtx ∀ᵇ Φᴿ ⊢ E ⊑ B →
   Φᴼ ⊢ `∀ E ⊑ `∀ C) →
  Φᴼ ⊢ D ⊑ `∀ C
forall-forall-support-dispatch support
    (ff-via-∀∀ E⊑A E⊑B) k∀∀ =
  k∀∀ E⊑A E⊑B
forall-forall-support-dispatch support
    (ff-via-∀ν {occC = occE} {occA = occA} E⊑A E⊑∀B) k∀∀ =
  k∀ν support E⊑A occE occA E⊑∀B
forall-forall-support-dispatch support
    (ff-via-ν∀ {occC = occE} {occB = occB} E⊑∀A E⊑B) k∀∀ =
  kν∀ support occE E⊑∀A E⊑B occB
forall-forall-support-dispatch support
    (ff-via-νν occE E⊑∀A E⊑∀B) k∀∀ =
  kνν support occE E⊑∀A E⊑∀B

forall-forall-support-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C D} →
  LiftMlb∀∀Support Φᴸ Φᴿ Φᴼ A B C →
  (∀ {E} →
   liftCtx ∀ᵇ Φᴸ ⊢ E ⊑ A →
   liftCtx ∀ᵇ Φᴿ ⊢ E ⊑ B →
   Φᴼ ⊢ `∀ E ⊑ `∀ C) →
  Φᴸ ⊢ D ⊑ `∀ A →
  Φᴿ ⊢ D ⊑ `∀ B →
  Φᴼ ⊢ D ⊑ `∀ C
forall-forall-support-open support k∀∀ D⊑∀A D⊑∀B =
  forall-forall-support-dispatch support
    (forall-forall-lower²-invᶜ D⊑∀A D⊑∀B)
    k∀∀

------------------------------------------------------------------------
-- Generalized lower-bound driven selector
------------------------------------------------------------------------

-- The old proof tried to choose an MLB by first splitting on the endpoint
-- shapes.  The active direction is instead to recurse on the two lower-bound
-- derivations.
--
-- `MlbCtx` is the compatibility invariant for the contexts used by the two
-- lower-bound proofs and by the output maximality comparison.  It is generated
-- from the identity imprecision context and records the binder mode used each
-- time the proof goes under `∀ⁱ` or `ν`.

data MlbCtx : ImpCtx → ImpCtx → ImpCtx → Set where
  idᵐ : ∀ Δ → MlbCtx (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
  lift∀∀ᵐ :
    ∀ {Φᴸ Φᴿ Φᴼ} →
    MlbCtx Φᴸ Φᴿ Φᴼ →
    MlbCtx (liftCtx ∀ᵇ Φᴸ) (liftCtx ∀ᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)
  lift∀νᵐ :
    ∀ {Φᴸ Φᴿ Φᴼ} →
    MlbCtx Φᴸ Φᴿ Φᴼ →
    MlbCtx (liftCtx ∀ᵇ Φᴸ) (liftCtx νᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)
  liftν∀ᵐ :
    ∀ {Φᴸ Φᴿ Φᴼ} →
    MlbCtx Φᴸ Φᴿ Φᴼ →
    MlbCtx (liftCtx νᵇ Φᴸ) (liftCtx ∀ᵇ Φᴿ) (liftCtx ∀ᵇ Φᴼ)

MlbCtx-vars :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  MlbCtx Φᴸ Φᴿ Φᴼ →
  MlbVarCtx Φᴸ Φᴿ Φᴼ
MlbCtx-vars (idᵐ Δ) = MlbVarCtx-idᵢ Δ
MlbCtx-vars (lift∀∀ᵐ Ψ) = MlbVarCtx-∀∀ (MlbCtx-vars Ψ)
MlbCtx-vars (lift∀νᵐ Ψ) = MlbVarCtx-∀ν (MlbCtx-vars Ψ)
MlbCtx-vars (liftν∀ᵐ Ψ) = MlbVarCtx-ν∀ (MlbCtx-vars Ψ)

maximal-var-varᵐ :
  ∀ {Φᴸ Φᴿ Φᴼ W X Y} →
  MlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (＇ X) (＇ Y)
maximal-var-varᵐ Ψ w⊑x w⊑y =
  maximal-var-varᶜ (MlbCtx-vars Ψ) w⊑x w⊑y

maximal-var-starᵐ :
  ∀ {Φᴸ Φᴿ Φᴼ W X} →
  MlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑★) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (＇ X) ★
maximal-var-starᵐ Ψ w⊑x w⊑★ =
  maximal-var-starᶜ (MlbCtx-vars Ψ) w⊑x w⊑★

maximal-star-varᵐ :
  ∀ {Φᴸ Φᴿ Φᴼ W Y} →
  MlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑★) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ ★ (＇ Y)
maximal-star-varᵐ Ψ w⊑★ w⊑y =
  maximal-star-varᶜ (MlbCtx-vars Ψ) w⊑★ w⊑y

postulate
  choose-mlbᶜ :
    ∀ {Φᴸ Φᴿ Φᴼ A B C} →
    MlbCtx Φᴸ Φᴿ Φᴼ →
    Φᴸ ⊢ C ⊑ A →
    Φᴿ ⊢ C ⊑ B →
    MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A B

choose-mlb-from-lower :
  ∀ {Δ A B C} →
  idᵢ Δ ⊢ C ⊑ A →
  idᵢ Δ ⊢ C ⊑ B →
  MaximalLowerBound Δ A B
choose-mlb-from-lower {Δ = Δ} C⊑A C⊑B
    with choose-mlbᶜ (idᵐ Δ) C⊑A C⊑B
choose-mlb-from-lower {Δ = Δ} C⊑A C⊑B | mlbᶜ =
  record
    { lower = lowerᶜ mlbᶜ
    ; lower-left = lower-leftᶜ mlbᶜ
    ; lower-right = lower-rightᶜ mlbᶜ
    ; maximal = maximalᶜ mlbᶜ
    }

choose-mlb :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  MaximalLowerBound Δ A B
choose-mlb (C , C⊑A , C⊑B) = choose-mlb-from-lower C⊑A C⊑B
