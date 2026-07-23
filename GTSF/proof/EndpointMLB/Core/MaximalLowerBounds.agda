module proof.EndpointMLB.Core.MaximalLowerBounds where

-- File Charter:
--   * Reusable maximal-lower-bound proof infrastructure for GTSF imprecision.
--   * Covers identity-context facts, base/star/type-variable maximality, and
--     arrow composition for lower bounds.
--   * Does not synthesize coercions or allocate stores.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; zero; suc; z<s; s<s; _≟_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Maybe using (Maybe; nothing; just)

open import Types
open import Imprecision
  using
    ( ImpAssm
    ; ImpCtx
    ; _ˣ⊑★
    ; _ˣ⊑ˣ_
    ; ⇑ᵢₐ
    ; ⇑ᵢ
    ; ⇑ᴸᵢₐ
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
    ; tag_⇛_
    ; ν
    )
open import proof.Core.Properties.ImprecisionProperties using (⊑-refl-idᵢ; ⊑-tgt-wf-idᵢ)
open import proof.Core.Properties.TypeProperties
  using
    ( TyRenameWf
    ; occurs-zero-rename-ext
    ; rename-cong
    ; renameᵗ-compose
    ; renameᵗ-id
    ; renameᵗ-preserves-WfTy
    )

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

data CAssm : Set where
  _~ᶜ★ : TyVar → CAssm
  ★~ᶜ_ : TyVar → CAssm
  _~ᶜ_ : TyVar → TyVar → CAssm

assm-left-assm : CAssm → ImpAssm
assm-left-assm (X ~ᶜ Y) = X ˣ⊑ˣ X
assm-left-assm (X ~ᶜ★) = X ˣ⊑ˣ X
assm-left-assm (★~ᶜ Y) = Y ˣ⊑★

assm-right-assm : CAssm → ImpAssm
assm-right-assm (X ~ᶜ Y) = X ˣ⊑ˣ Y
assm-right-assm (X ~ᶜ★) = X ˣ⊑★
assm-right-assm (★~ᶜ Y) = Y ˣ⊑ˣ Y

assm-left : List CAssm → ImpCtx
assm-left [] = []
assm-left (a ∷ Γ) = assm-left-assm a ∷ assm-left Γ

assm-right : List CAssm → ImpCtx
assm-right [] = []
assm-right (a ∷ Γ) = assm-right-assm a ∷ assm-right Γ

clash? : CAssm → CAssm → Bool
clash? (X ~ᶜ Y) (X′ ~ᶜ Y′) with X ≟ X′ | Y ≟ Y′
clash? (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | yes _ = false
clash? (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | no _ = true
clash? (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | yes _ = true
clash? (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | no _ = false
clash? (X ~ᶜ Y) (X′ ~ᶜ★) with X ≟ X′
clash? (X ~ᶜ Y) (X′ ~ᶜ★) | yes _ = true
clash? (X ~ᶜ Y) (X′ ~ᶜ★) | no _ = false
clash? (X ~ᶜ Y) (★~ᶜ Y′) with Y ≟ Y′
clash? (X ~ᶜ Y) (★~ᶜ Y′) | yes _ = true
clash? (X ~ᶜ Y) (★~ᶜ Y′) | no _ = false
clash? (X ~ᶜ★) (X′ ~ᶜ Y′) with X ≟ X′
clash? (X ~ᶜ★) (X′ ~ᶜ Y′) | yes _ = true
clash? (X ~ᶜ★) (X′ ~ᶜ Y′) | no _ = false
clash? (X ~ᶜ★) (X′ ~ᶜ★) = false
clash? (X ~ᶜ★) (★~ᶜ Y′) = false
clash? (★~ᶜ Y) (X′ ~ᶜ Y′) with Y ≟ Y′
clash? (★~ᶜ Y) (X′ ~ᶜ Y′) | yes _ = true
clash? (★~ᶜ Y) (X′ ~ᶜ Y′) | no _ = false
clash? (★~ᶜ Y) (X′ ~ᶜ★) = false
clash? (★~ᶜ Y) (★~ᶜ Y′) = false

same-assm? : CAssm → CAssm → Bool
same-assm? (X ~ᶜ★) (X′ ~ᶜ★) with X ≟ X′
same-assm? (X ~ᶜ★) (X′ ~ᶜ★) | yes _ = true
same-assm? (X ~ᶜ★) (X′ ~ᶜ★) | no _ = false
same-assm? (X ~ᶜ★) (★~ᶜ Y′) = false
same-assm? (X ~ᶜ★) (X′ ~ᶜ Y′) = false
same-assm? (★~ᶜ Y) (X′ ~ᶜ★) = false
same-assm? (★~ᶜ Y) (★~ᶜ Y′) with Y ≟ Y′
same-assm? (★~ᶜ Y) (★~ᶜ Y′) | yes _ = true
same-assm? (★~ᶜ Y) (★~ᶜ Y′) | no _ = false
same-assm? (★~ᶜ Y) (X′ ~ᶜ Y′) = false
same-assm? (X ~ᶜ Y) (X′ ~ᶜ★) = false
same-assm? (X ~ᶜ Y) (★~ᶜ Y′) = false
same-assm? (X ~ᶜ Y) (X′ ~ᶜ Y′) with X ≟ X′ | Y ≟ Y′
same-assm? (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | yes _ = true
same-assm? (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | no _ = false
same-assm? (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | yes _ = false
same-assm? (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | no _ = false

insert-assm : CAssm → List CAssm → Maybe (List CAssm)
insert-assm a [] = just (a ∷ [])
insert-assm a (b ∷ Γ)
    with same-assm? a b | clash? a b
... | true | _ = just (b ∷ Γ)
... | false | true = nothing
... | false | false
    with insert-assm a Γ
... | nothing = nothing
... | just Γ′ = just (b ∷ Γ′)

merge-assms : List CAssm → List CAssm → Maybe (List CAssm)
merge-assms [] Γ′ = just Γ′
merge-assms (a ∷ Γ) Γ′
    with merge-assms Γ Γ′
... | nothing = nothing
... | just Γ″ = insert-assm a Γ″

add∀ : ℕ → Ty → Ty
add∀ zero A = A
add∀ (suc n) A = `∀ (add∀ n A)

split-∀-rebuild-direct :
  (A : Ty) →
  A ≡ add∀ (proj₁ (split-∀ A)) (proj₁ (proj₂ (split-∀ A)))
split-∀-rebuild-direct (＇ X) = refl
split-∀-rebuild-direct (‵ ι) = refl
split-∀-rebuild-direct ★ = refl
split-∀-rebuild-direct (A ⇒ B) = refl
split-∀-rebuild-direct (`∀ A)
    with split-∀ A | split-∀-rebuild-direct A
split-∀-rebuild-direct (`∀ A)
    | n , B , n∀ | eq =
  cong `∀ eq

split-∀-rebuild :
  ∀ {A n A′ n∀A′} →
  split-∀ A ≡ (n , A′ , n∀A′) →
  A ≡ add∀ n A′
split-∀-rebuild {A = A} eq =
  subst
    (λ p → A ≡ add∀ (proj₁ p) (proj₁ (proj₂ p)))
    eq
    (split-∀-rebuild-direct A)

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

bound-var-var? : ℕ → ℕ → CAssm → Bool
bound-var-var? n m (X ~ᶜ Y) with X <? n | right-bound? n m Y
... | yes _ | true = true
... | yes _ | false = false
... | no _ | _ = false
bound-var-var? n m (X ~ᶜ★) = false
bound-var-var? n m (★~ᶜ Y) = false

discharged-assm? : ℕ → ℕ → CAssm → Bool
discharged-assm? n m (X ~ᶜ Y) = bound-var-var? n m (X ~ᶜ Y)
discharged-assm? n m (X ~ᶜ★) with X <? n
... | yes _ = true
... | no _ = false
discharged-assm? n m (★~ᶜ Y) = right-bound? n m Y

escapes-local? : ℕ → ℕ → CAssm → Bool
escapes-local? n m (X ~ᶜ Y) with X <? n | right-bound? n m Y
... | yes _ | true = false
... | yes _ | false = true
... | no _ | true = true
... | no _ | false = false
escapes-local? n m (X ~ᶜ★) = false
escapes-local? n m (★~ᶜ Y) = false

no-escaping-assms? : ℕ → ℕ → List CAssm → Bool
no-escaping-assms? n m [] = true
no-escaping-assms? n m (a ∷ Γ) with escapes-local? n m a
... | true = false
... | false = no-escaping-assms? n m Γ

bound-var-var-order-ok? : CAssm → CAssm → Bool
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    with X <? X′ | X′ <? X | Y <? Y′ | Y′ <? Y
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    | yes _ | _ | yes _ | _ = true
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    | yes _ | _ | no _ | _ = false
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    | no _ | yes _ | _ | yes _ = true
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    | no _ | yes _ | _ | no _ = false
bound-var-var-order-ok? (X ~ᶜ Y) (X′ ~ᶜ Y′)
    | no _ | no _ | _ | _ = true
bound-var-var-order-ok? _ _ = true

bound-var-var-order-ok-with? :
  ℕ → ℕ → CAssm → List CAssm → Bool
bound-var-var-order-ok-with? n m a [] = true
bound-var-var-order-ok-with? n m a (a′ ∷ Γ)
    with bound-var-var? n m a | bound-var-var? n m a′
... | true | true
    with bound-var-var-order-ok? a a′
... | true = bound-var-var-order-ok-with? n m a Γ
... | false = false
bound-var-var-order-ok-with? n m a (a′ ∷ Γ) | _ | _ =
  bound-var-var-order-ok-with? n m a Γ

bound-var-var-order-ok-list? : ℕ → ℕ → List CAssm → Bool
bound-var-var-order-ok-list? n m [] = true
bound-var-var-order-ok-list? n m (a ∷ Γ)
    with bound-var-var-order-ok-with? n m a Γ
... | true = bound-var-var-order-ok-list? n m Γ
... | false = false

bound-var-var-count : ℕ → ℕ → List CAssm → ℕ
bound-var-var-count n m [] = zero
bound-var-var-count n m (a ∷ Γ) with bound-var-var? n m a
... | true = suc (bound-var-var-count n m Γ)
... | false = bound-var-var-count n m Γ

find-left-for-right : TyVar → List CAssm → Maybe TyVar
find-left-for-right Y [] = nothing
find-left-for-right Y ((X ~ᶜ Y′) ∷ Γ) with Y ≟ Y′
... | yes _ = just X
... | no _ = find-left-for-right Y Γ
find-left-for-right Y ((X ~ᶜ★) ∷ Γ) = find-left-for-right Y Γ
find-left-for-right Y ((★~ᶜ Y′) ∷ Γ) = find-left-for-right Y Γ

find-right-for-left : TyVar → List CAssm → Maybe TyVar
find-right-for-left X [] = nothing
find-right-for-left X ((X′ ~ᶜ Y) ∷ Γ) with X ≟ X′
... | yes _ = just Y
... | no _ = find-right-for-left X Γ
find-right-for-left X ((X′ ~ᶜ★) ∷ Γ) = find-right-for-left X Γ
find-right-for-left X ((★~ᶜ Y) ∷ Γ) = find-right-for-left X Γ

find-bound-right-for-left :
  ℕ → ℕ → TyVar → List CAssm → Maybe TyVar
find-bound-right-for-left n m X Γ with find-right-for-left X Γ
... | nothing = nothing
... | just Y with right-bound? n m Y
... | true = just Y
... | false = nothing

matched-right? : TyVar → List CAssm → Bool
matched-right? Y [] = false
matched-right? Y ((X ~ᶜ Y′) ∷ Γ) with Y ≟ Y′
... | yes _ = true
... | no _ = matched-right? Y Γ
matched-right? Y ((X ~ᶜ★) ∷ Γ) = matched-right? Y Γ
matched-right? Y ((★~ᶜ Y′) ∷ Γ) = matched-right? Y Γ

unmatched-right-before : ℕ → ℕ → List CAssm → ℕ
unmatched-right-before n zero Γ = zero
unmatched-right-before n (suc Y) Γ
    with matched-right? (n + Y) Γ
... | true = unmatched-right-before n Y Γ
... | false = suc (unmatched-right-before n Y Γ)

last-bound-right-before-left :
  ℕ → ℕ → List CAssm → TyVar → Maybe TyVar
last-bound-right-before-left n m Γ zero = nothing
last-bound-right-before-left n m Γ (suc X)
    with last-bound-right-before-left n m Γ X
       | find-bound-right-for-left n m X Γ
... | _ | just Y = just Y
... | prev | nothing = prev

unmatched-rights-before-left :
  ℕ → ℕ → List CAssm → TyVar → ℕ
unmatched-rights-before-left n m Γ X
    with find-bound-right-for-left n m X Γ
... | just Y = unmatched-right-before n (Y ∸ n) Γ
... | nothing
    with last-bound-right-before-left n m Γ X
... | just Y = unmatched-right-before n (Y ∸ n) Γ
... | nothing = zero

rightOnlys-count : ℕ → ℕ → ℕ
rightOnlys-count zero rest = rest
rightOnlys-count (suc k) rest = suc (rightOnlys-count k rest)

left-output-spine-count-from :
  ℕ → ℕ → List CAssm → ℕ → TyVar → ℕ → ℕ
left-output-spine-count-from n m Γ zero X emitted =
  rightOnlys-count (unmatched-right-before n m Γ ∸ emitted) zero
left-output-spine-count-from n m Γ (suc fuel) X emitted
    with unmatched-rights-before-left n m Γ X
... | before =
  rightOnlys-count (before ∸ emitted)
    (suc (left-output-spine-count-from n m Γ fuel (suc X) before))

mlb-∀-count : ℕ → ℕ → List CAssm → ℕ
mlb-∀-count n m Γ =
  left-output-spine-count-from n m Γ n zero zero

normalize-left-var : ℕ → ℕ → List CAssm → TyVar → TyVar
normalize-left-var n m Γ X = X + unmatched-rights-before-left n m Γ X

left-binders-before-right-from :
  ℕ → ℕ → List CAssm → TyVar → ℕ → TyVar → ℕ
left-binders-before-right-from n m Γ Y zero X = X
left-binders-before-right-from n m Γ Y (suc fuel) X
    with find-bound-right-for-left n m X Γ
... | nothing =
  left-binders-before-right-from n m Γ Y fuel (suc X)
... | just Y′ with Y <? Y′
... | yes _ = X
... | no _ =
  left-binders-before-right-from n m Γ Y fuel (suc X)

left-binders-before-right : ℕ → ℕ → List CAssm → TyVar → ℕ
left-binders-before-right n m Γ Y =
  left-binders-before-right-from n m Γ Y n zero

normalize-var : ℕ → ℕ → List CAssm → TyVar → TyVar
normalize-var n m Γ X with X <? n | X <? (n + m)
... | yes _ | _ = normalize-left-var n m Γ X
... | no _ | yes _
    with find-left-for-right X Γ
... | just Y = normalize-left-var n m Γ Y
... | nothing =
  left-binders-before-right n m Γ X + unmatched-right-before n (X ∸ n) Γ
normalize-var n m Γ X | no _ | no _ =
  mlb-∀-count n m Γ + (X ∸ (n + m))

identity-assm? : CAssm → Bool
identity-assm? (X ~ᶜ Y) with X ≟ Y
... | yes _ = true
... | no _ = false
identity-assm? (X ~ᶜ★) = false
identity-assm? (★~ᶜ Y) = false

residual-var : ℕ → ℕ → TyVar → TyVar
residual-var n m X with X <? (n + m)
... | yes _ = X
... | no _ = X ∸ (n + m)

normalize-assm : ℕ → ℕ → List CAssm → CAssm → CAssm
normalize-assm n m Γ (X ~ᶜ Y) =
  residual-var n m X ~ᶜ residual-var n m Y
normalize-assm n m Γ (X ~ᶜ★) = residual-var n m X ~ᶜ★
normalize-assm n m Γ (★~ᶜ Y) = ★~ᶜ residual-var n m Y

normalize-assm-ctx-irrelevant :
  ∀ n m Γ Γ′ a →
  normalize-assm n m Γ a ≡ normalize-assm n m Γ′ a
normalize-assm-ctx-irrelevant n m Γ Γ′ (X ~ᶜ Y) = refl
normalize-assm-ctx-irrelevant n m Γ Γ′ (X ~ᶜ★) = refl
normalize-assm-ctx-irrelevant n m Γ Γ′ (★~ᶜ Y) = refl

normalize-assms-clash-check :
  ℕ → ℕ → List CAssm → Maybe (List CAssm)
normalize-assms-clash-check n m [] = just []
normalize-assms-clash-check n m (a ∷ Γ)
    with normalize-assms-clash-check n m Γ
... | nothing = nothing
... | just Γ′ =
  insert-assm (normalize-assm n m (a ∷ Γ) a) Γ′

normalize-assms-residual :
  ℕ → ℕ → List CAssm → Maybe (List CAssm)
normalize-assms-residual n m [] = just []
normalize-assms-residual n m (a ∷ Γ)
    with normalize-assms-residual n m Γ | discharged-assm? n m a
... | nothing | _ = nothing
... | just Γ′ | true = just Γ′
... | just Γ′ | false
    with normalize-assm n m (a ∷ Γ) a
... | a′ = insert-assm a′ Γ′

normalize-assms :
  ℕ → ℕ → List CAssm → Maybe (List CAssm)
normalize-assms n m Γ
    with normalize-assms-clash-check n m Γ
... | nothing = nothing
... | just _ = normalize-assms-residual n m Γ

residual-assms-ok? : List CAssm → Bool
residual-assms-ok? [] = true
residual-assms-ok? (a ∷ Γ) with identity-assm? a
... | true = residual-assms-ok? Γ
... | false = false

foralls-used? : Ty → Bool
foralls-used? (＇ X) = true
foralls-used? (‵ ι) = true
foralls-used? ★ = true
foralls-used? (A ⇒ B) with foralls-used? A | foralls-used? B
... | true | true = true
... | true | false = false
... | false | true = false
... | false | false = false
foralls-used? (`∀ A) with occurs zero A | foralls-used? A
... | true | true = true
... | true | false = false
... | false | true = false
... | false | false = false

mutual
  {-# TERMINATING #-}
  search-mlb? : (A B : Ty) → Maybe (Ty × List CAssm)
  search-mlb? A B
      with split-∀ A | split-∀ B
  ... | n , A′ , n∀A′ | m , B′ , n∀B′
      with core-mlb?
             (renameᵗ (embed-left-var n m) A′)
             (renameᵗ (embed-right-var n m) B′)
             (rename-non∀ n∀A′)
             (rename-non∀ n∀B′)
  ... | nothing = nothing
  ... | just (C , Γ)
      with no-escaping-assms? n m Γ
  ... | false = nothing
  ... | true
      with bound-var-var-order-ok-list? n m Γ
  ... | false = nothing
  ... | true
      with normalize-assms n m Γ
  ... | nothing = nothing
  ... | just Γ′
      with add∀ (mlb-∀-count n m Γ) (renameᵗ (normalize-var n m Γ) C)
  ... | C′ with foralls-used? C′
  ... | true = just (C′ , Γ′)
  ... | false = nothing

  core-mlb? : (A B : Ty) → Non∀ A → Non∀ B → Maybe (Ty × List CAssm)
  core-mlb? (＇ X) (＇ Y) n∀A n∀B = just ((＇ X) , (X ~ᶜ Y) ∷ [])
  core-mlb? (＇ X) (‵ ι) n∀A n∀B = nothing
  core-mlb? (＇ X) ★ n∀A n∀B = just ((＇ X) , (X ~ᶜ★) ∷ [])
  core-mlb? (＇ X) (B₁ ⇒ B₂) n∀A n∀B = nothing
  core-mlb? (‵ ι) (＇ x) n∀A n∀B = nothing
  core-mlb? (‵ ι₁) (‵ ι₂) n∀A n∀B
      with ι₁ ≟Base ι₂
  ... | yes refl = just (‵ ι₁ , [])
  ... | no neq = nothing
  core-mlb? (‵ ι) ★ n∀A n∀B = just ((‵ ι) , [])
  core-mlb? (‵ ι) (B₁ ⇒ B₂) n∀A n∀B = nothing
  core-mlb? ★ (＇ Y) n∀A n∀B = just ((＇ Y) , (★~ᶜ Y) ∷ [])
  core-mlb? ★ (‵ ι) n∀A n∀B = just ((‵ ι) , [])
  core-mlb? ★ ★ n∀A n∀B = just (★ , [])
  core-mlb? ★ (B₁ ⇒ B₂) n∀A n∀B
      with search-mlb? ★ B₁ | search-mlb? ★ B₂
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂
  ... | nothing = nothing
  ... | just Γ = just (C₁ ⇒ C₂ , Γ)
  core-mlb? ★ (`∀ B) n∀A ()
  core-mlb? (A₁ ⇒ A₂) (＇ X) n∀A n∀B = nothing
  core-mlb? (A₁ ⇒ A₂) (‵ ι) n∀A n∀B = nothing
  core-mlb? (A₁ ⇒ A₂) ★ n∀A n∀B
      with search-mlb? A₁ ★ | search-mlb? A₂ ★
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂
  ... | nothing = nothing
  ... | just Γ = just (C₁ ⇒ C₂ , Γ)
  core-mlb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) n∀A n∀B
      with search-mlb? A₁ B₁ | search-mlb? A₂ B₂
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂
  ... | nothing = nothing
  ... | just Γ = just (C₁ ⇒ C₂ , Γ)
  core-mlb? (A₁ ⇒ A₂) (`∀ B) n∀A ()


mlb? : (A B : Ty) → Maybe Ty
mlb? A B with search-mlb? A B
... | nothing = nothing
... | just (C , Γ) with residual-assms-ok? Γ
... | true = just C
... | false = nothing

------------------------------------------------------------------------
-- Proof skeleton for `mlb?` lower-bound soundness
------------------------------------------------------------------------

-- The target theorem for the executable `mlb?` procedure is:
--
-- mlb?-lower :
--   ∀ {Δ A B C} →
--   WfTy Δ A →
--   WfTy Δ B →
--   mlb? A B ≡ just C →
--   idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
--
-- The proof should go through `search-mlb?`:
--
-- search-mlb?-lower :
--   ∀ {Δ A B C Γ} →
--   WfTy Δ A →
--   WfTy Δ B →
--   search-mlb? A B ≡ just (C , Γ) →
--   residual-assms-ok? Γ ≡ true →
--   idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
--
-- The main invariant should interpret the `CAssm` list as the variable
-- assumptions needed by the raw result from `core-mlb?`.  A useful proof
-- view is an output-binder spine:
--
-- data OutBinder : Set where
--   both      : OutBinder
--   leftOnly  : OutBinder
--   rightOnly : OutBinder
--
-- The `both` case is wrapped with `∀ⁱ` on both sides.  The `leftOnly`
-- case is wrapped with `∀ⁱ` on the left and `ν` on the right.  The
-- `rightOnly` case is wrapped with `ν` on the left and `∀ⁱ` on the
-- right.
--
-- AssmCtx Φᴸ Φᴿ Γ should say that each `CAssm` in Γ has the
-- corresponding imprecision evidence:
--
--   X ~ᶜ Y  :  Φᴸ contains X ˣ⊑ˣ X and Φᴿ contains X ˣ⊑ˣ Y
--   X ~ᶜ★   :  Φᴸ contains X ˣ⊑ˣ X and Φᴿ contains X ˣ⊑★
--   ★~ᶜ Y   :  Φᴸ contains Y ˣ⊑★   and Φᴿ contains Y ˣ⊑ˣ Y
--
-- Lemmas for `split-∀`:
--
-- split-∀-rebuild :
--   split-∀ A ≡ (n , A′ , n∀A′) →
--   A ≡ add∀ n A′
--
-- split-∀-wf :
--   WfTy Δ A →
--   split-∀ A ≡ (n , A′ , n∀A′) →
--   WfTy (n + Δ) A′
--
-- Lemmas for `add∀` and `foralls-used?`:
--
-- foralls-used?-sound :
--   foralls-used? A ≡ true →
--   -- every `∀` in A has the occurrence proof needed by `wf∀`/`∀ⁱ`/`ν`.
--
-- add∀-lower :
--   -- Given the output-binder spine and a body lower-bound proof under the
--   -- corresponding lifted contexts, build the two lower-bound proofs for
--   -- `add∀ k C` below the original split inputs.
--
-- Lemmas for `rename-non∀`:
--
-- rename-non∀-sound :
--   (n∀A : Non∀ A) →
--   Non∀ (renameᵗ ρ A)
--
-- Lemmas for `embed-left-var` and `embed-right-var`:
--
-- embed-left-var-bound :
--   X < n →
--   embed-left-var n m X ≡ X
--
-- embed-left-var-free :
--   n ≤ X →
--   embed-left-var n m X ≡ n + m + (X ∸ n)
--
-- embed-right-var-bound :
--   Y < m →
--   embed-right-var n m Y ≡ n + Y
--
-- embed-right-var-free :
--   m ≤ Y →
--   embed-right-var n m Y ≡ n + m + (Y ∸ m)
--
-- embed-left-wf :
--   WfTy (n + Δ) A →
--   WfTy (n + m + Δ) (renameᵗ (embed-left-var n m) A)
--
-- embed-right-wf :
--   WfTy (m + Δ) B →
--   WfTy (n + m + Δ) (renameᵗ (embed-right-var n m) B)
--
-- Lemmas for `clash?`, `same-assm?`, `insert-assm`, and `merge-assms`:
--
-- same-assm?-sound :
--   same-assm? a b ≡ true →
--   a ≡ b
--
-- clash?-sound :
--   clash? a b ≡ true →
--   -- a and b cannot both be satisfied by one coherent binder merge.
--
-- insert-assm-preserves :
--   insert-assm a Γ ≡ just Γ′ →
--   -- Γ′ contains a and preserves every assumption from Γ, up to dedup.
--
-- insert-assm-no-clash :
--   insert-assm a Γ ≡ just Γ′ →
--   -- Γ′ remains pairwise clash-free.
--
-- merge-assms-preserves :
--   merge-assms Γ₁ Γ₂ ≡ just Γ →
--   -- Γ contains assumptions from Γ₁ and Γ₂, up to dedup.
--
-- merge-assms-no-clash :
--   merge-assms Γ₁ Γ₂ ≡ just Γ →
--   -- Γ remains pairwise clash-free.
--
-- Lemmas for `right-bound?`, `bound-var-var?`, and `discharged-assm?`:
--
-- right-bound?-sound :
--   right-bound? n m Y ≡ true →
--   n ≤ Y × Y < n + m
--
-- bound-var-var?-sound :
--   bound-var-var? n m a ≡ true →
--   ∃[ X ] ∃[ Y ]
--     a ≡ X ~ᶜ Y × X < n × right-bound? n m Y ≡ true
--
-- discharged-assm?-sound :
--   discharged-assm? n m a ≡ true →
--   -- a is accounted for by a local output forall binder.
--
-- Lemmas for `escapes-local?` and `no-escaping-assms?`:
--
-- escapes-local?-sound :
--   escapes-local? n m a ≡ true →
--   -- a is a local/nonlocal variable equation and cannot safely escape.
--
-- no-escaping-assms?-sound :
--   no-escaping-assms? n m Γ ≡ true →
--   -- every non-discharged var-var assumption is fully nonlocal.
--
-- Lemmas for binder ordering and counting:
--
-- bound-var-var-order-ok?-sound :
--   bound-var-var-order-ok? a b ≡ true →
--   -- matched local binder pairs preserve left/right order.
--
-- bound-var-var-order-ok-with?-sound :
--   bound-var-var-order-ok-with? n m a Γ ≡ true →
--   -- a is order-compatible with all matched local assumptions in Γ.
--
-- bound-var-var-order-ok-list?-sound :
--   bound-var-var-order-ok-list? n m Γ ≡ true →
--   -- all matched local binder pairs in Γ are order-preserving.
--
-- bound-var-var-count-sound :
--   bound-var-var-count n m Γ ≡ k →
--   -- k is the number of matched local binder pairs.
--
-- mlb-∀-count-sound :
--   mlb-∀-count n m Γ ≡ k →
--   -- k = left binders + right binders - matched binder pairs.
--
-- Lemmas for lookup and position helpers:
--
-- find-left-for-right-sound :
--   find-left-for-right Y Γ ≡ just X →
--   (X ~ᶜ Y) ∈ Γ
--
-- find-right-for-left-sound :
--   find-right-for-left X Γ ≡ just Y →
--   (X ~ᶜ Y) ∈ Γ
--
-- find-bound-right-for-left-sound :
--   find-bound-right-for-left n m X Γ ≡ just Y →
--   (X ~ᶜ Y) ∈ Γ × right-bound? n m Y ≡ true
--
-- matched-right?-sound :
--   matched-right? Y Γ ≡ true →
--   ∃[ X ] (X ~ᶜ Y) ∈ Γ
--
-- unmatched-right-before-sound :
--   -- `unmatched-right-before n Y Γ` counts right binders before `n + Y`
--   -- that are not matched by Γ.
--
-- last-bound-right-before-left-sound :
--   -- If this returns `just Y`, then Y is the last right binder matched by
--   -- some left binder strictly before X.
--
-- unmatched-rights-before-left-sound :
--   -- Counts right-only output binders that must appear before a left binder.
--
-- normalize-left-var-sound :
--   -- Gives the output binder position for a local left binder.
--
-- left-binders-before-right-from-sound :
--   -- Accumulator lemma for `left-binders-before-right`.
--
-- left-binders-before-right-sound :
--   -- Counts left output binders that must appear before a right-only binder.
--
-- Lemmas for `normalize-var`, `normalize-assm`, and `normalize-assms`:
--
-- normalize-var-left-bound :
--   X < n →
--   -- `normalize-var n m Γ X` is the output position for left binder X.
--
-- normalize-var-right-bound :
--   right-bound? n m Y ≡ true →
--   -- `normalize-var n m Γ Y` is the matched-left position, or the
--   -- right-only output position when Y is unmatched.
--
-- normalize-var-free :
--   n + m ≤ X →
--   -- Free variables are shifted past all output foralls.
--
-- identity-assm?-sound :
--   identity-assm? a ≡ true →
--   ∃[ X ] a ≡ X ~ᶜ X
--
-- normalize-assm-sound :
--   normalize-assm n m Γ a ≡ a′ →
--   -- a′ is a normalized form of a under `normalize-var n m Γ`.
--
-- normalize-assms-sound :
--   normalize-assms n m Γ ≡ just Γ′ →
--   -- Γ′ is the residual assumption list: discharged local binder
--   -- assumptions and normalized identities have been removed, and the
--   -- remaining normalized assumptions are clash-free.
--
-- The body proof cannot be transported directly into `assm-left Γ′` and
-- `assm-right Γ′`: discharged assumptions are still needed until the
-- output `∀` spine is introduced.  Instead, normalization first transports
-- into an explicit pending-spine context containing every raw assumption
-- after `normalize-var`.  The `add∀` proof then consumes the discharged
-- assumptions from that pending context while wrapping the output binders.
--
-- The proof-facing `left-output-spine` walks the left local binders in order.
-- Before each left binder X it inserts the unmatched right-only binders
-- counted by `unmatched-rights-before-left`; then it emits `both` when
-- `find-bound-right-for-left` finds a bound right partner and `leftOnly`
-- otherwise.  After all left binders, it appends the remaining unmatched
-- right-only binders counted by `unmatched-right-before`.
--
-- The soundness lemmas for that concrete spine require the same guards that
-- `search-mlb?` has already checked: no local/nonlocal escaping assumptions,
-- order compatibility for matched local binders, and successful normalization.
--
-- residual-assms-ok?-sound :
--   residual-assms-ok? Γ ≡ true →
--   -- every residual assumption is an identity `X ~ᶜ X`.
--
-- Core proof theorem:
--
-- core-mlb?-lower-raw :
--   core-mlb? A B n∀A n∀B ≡ just (C , Γ) →
--   AssmCtx Φᴸ Φᴿ Γ →
--   Φᴸ ⊢ C ⊑ A × Φᴿ ⊢ C ⊑ B
--
-- The variable cases consume one `CAssm`.  The base/star cases use `id★`,
-- `idι`, `tag`, `tag_⇛_`, and `tagˣ`.  The arrow cases use recursive
-- `search-mlb?-lower` results plus `merge-assms-preserves`.
--
-- Search proof theorem:
--
-- search-mlb?-lower should:
--   1. use `split-∀-rebuild` and `split-∀-wf`;
--   2. use `embed-left-wf` and `embed-right-wf`;
--   3. call `core-mlb?-lower-raw`;
--   4. use `no-escaping-assms?-sound`,
--      `bound-var-var-order-ok-list?-sound`, and `normalize-assms-sound`;
--   5. transport the raw proofs through `normalize-var` into the explicit
--      pending output-spine contexts;
--   6. use `add∀-lower` and `foralls-used?-sound` to wrap the output
--      binders and consume the pending assumptions down to the residual
--      contexts;
--   7. use `residual-assms-ok?-sound` to discharge remaining assumptions
--      into `idᵢ Δ`.
--
-- Top-level proof:
--
-- mlb?-lower follows by reducing `mlb? A B`, extracting the successful
-- `search-mlb? A B ≡ just (C , Γ)` branch, observing that the final guard
-- gives `residual-assms-ok? Γ ≡ true`, and calling `search-mlb?-lower`.

ForallsUsed : Ty → Set
ForallsUsed A = foralls-used? A ≡ true

data OutBinder : Set where
  both : OutBinder
  leftOnly : OutBinder
  rightOnly : OutBinder

OutputSpine : Set
OutputSpine = List OutBinder

wrap-output : OutputSpine → Ty → Ty
wrap-output [] A = A
wrap-output (_ ∷ bs) A = `∀ (wrap-output bs A)

reverse-local : ∀ {A : Set} → List A → List A
reverse-local [] = []
reverse-local (x ∷ xs) = reverse-local xs ++ (x ∷ [])

length-++-local :
  ∀ {A : Set} (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
length-++-local [] ys = refl
length-++-local (x ∷ xs) ys =
  cong suc (length-++-local xs ys)

++-assoc-local :
  ∀ {A : Set} (xs ys zs : List A) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc-local [] ys zs = refl
++-assoc-local (x ∷ xs) ys zs =
  cong (λ ws → x ∷ ws) (++-assoc-local xs ys zs)

+-one-right-local : ∀ n → n + 1 ≡ suc n
+-one-right-local zero = refl
+-one-right-local (suc n) = cong suc (+-one-right-local n)

length-reverse-local :
  ∀ {A : Set} (xs : List A) →
  length (reverse-local xs) ≡ length xs
length-reverse-local [] = refl
length-reverse-local (x ∷ xs) =
  trans
    (length-++-local (reverse-local xs) (x ∷ []))
    (trans
      (cong (λ k → k + 1) (length-reverse-local xs))
      (+-one-right-local (length xs)))

suc-injective-local : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-injective-local refl = refl

wrap-output-length :
  ∀ {bs A k} →
  length bs ≡ k →
  wrap-output bs A ≡ add∀ k A
wrap-output-length {bs = []} refl = refl
wrap-output-length {bs = _ ∷ _} {k = zero} ()
wrap-output-length {bs = _ ∷ bs} {k = suc k} eq =
  cong `∀ (wrap-output-length {bs = bs} (suc-injective-local eq))

wrap-left-target : OutputSpine → Ty → Ty
wrap-left-target [] A = A
wrap-left-target (both ∷ bs) A = `∀ (wrap-left-target bs A)
wrap-left-target (leftOnly ∷ bs) A = `∀ (wrap-left-target bs A)
wrap-left-target (rightOnly ∷ bs) A = wrap-left-target bs A

wrap-left-target-++ :
  ∀ bs cs A →
  wrap-left-target (bs ++ cs) A ≡
  wrap-left-target bs (wrap-left-target cs A)
wrap-left-target-++ [] cs A = refl
wrap-left-target-++ (both ∷ bs) cs A =
  cong `∀ (wrap-left-target-++ bs cs A)
wrap-left-target-++ (leftOnly ∷ bs) cs A =
  cong `∀ (wrap-left-target-++ bs cs A)
wrap-left-target-++ (rightOnly ∷ bs) cs A =
  wrap-left-target-++ bs cs A

wrap-left-target-∀ :
  ∀ bs A →
  wrap-left-target bs (`∀ A) ≡ `∀ (wrap-left-target bs A)
wrap-left-target-∀ [] A = refl
wrap-left-target-∀ (both ∷ bs) A =
  cong `∀ (wrap-left-target-∀ bs A)
wrap-left-target-∀ (leftOnly ∷ bs) A =
  cong `∀ (wrap-left-target-∀ bs A)
wrap-left-target-∀ (rightOnly ∷ bs) A =
  wrap-left-target-∀ bs A

wrap-left-target-reverse :
  ∀ bs A →
  wrap-left-target (reverse-local bs) A ≡ wrap-left-target bs A
wrap-left-target-reverse [] A = refl
wrap-left-target-reverse (both ∷ bs) A =
  trans
    (wrap-left-target-++ (reverse-local bs) (both ∷ []) A)
    (trans
      (wrap-left-target-reverse bs (`∀ A))
      (wrap-left-target-∀ bs A))
wrap-left-target-reverse (leftOnly ∷ bs) A =
  trans
    (wrap-left-target-++ (reverse-local bs) (leftOnly ∷ []) A)
    (trans
      (wrap-left-target-reverse bs (`∀ A))
      (wrap-left-target-∀ bs A))
wrap-left-target-reverse (rightOnly ∷ bs) A =
  trans
    (wrap-left-target-++ (reverse-local bs) (rightOnly ∷ []) A)
    (wrap-left-target-reverse bs A)

wrap-right-target : OutputSpine → Ty → Ty
wrap-right-target [] A = A
wrap-right-target (both ∷ bs) A = `∀ (wrap-right-target bs A)
wrap-right-target (leftOnly ∷ bs) A = wrap-right-target bs A
wrap-right-target (rightOnly ∷ bs) A = `∀ (wrap-right-target bs A)

left-spine-ctx : OutputSpine → ImpCtx → ImpCtx
left-spine-ctx [] Φ = Φ
left-spine-ctx (both ∷ bs) Φ =
  left-spine-ctx bs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
left-spine-ctx (leftOnly ∷ bs) Φ =
  left-spine-ctx bs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
left-spine-ctx (rightOnly ∷ bs) Φ =
  left-spine-ctx bs ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)

left-spine-ctx-++ :
  ∀ bs cs Φ →
  left-spine-ctx (bs ++ cs) Φ ≡
  left-spine-ctx cs (left-spine-ctx bs Φ)
left-spine-ctx-++ [] cs Φ = refl
left-spine-ctx-++ (both ∷ bs) cs Φ =
  left-spine-ctx-++ bs cs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
left-spine-ctx-++ (leftOnly ∷ bs) cs Φ =
  left-spine-ctx-++ bs cs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
left-spine-ctx-++ (rightOnly ∷ bs) cs Φ =
  left-spine-ctx-++ bs cs ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)

right-spine-ctx : OutputSpine → ImpCtx → ImpCtx
right-spine-ctx [] Φ = Φ
right-spine-ctx (both ∷ bs) Φ =
  right-spine-ctx bs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
right-spine-ctx (leftOnly ∷ bs) Φ =
  right-spine-ctx bs ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
right-spine-ctx (rightOnly ∷ bs) Φ =
  right-spine-ctx bs ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)

left-spine-source-var : OutputSpine → TyVar → TyVar
left-spine-source-var [] X = X
left-spine-source-var (_ ∷ bs) X = left-spine-source-var bs (suc X)

left-spine-target-var : OutputSpine → TyVar → TyVar
left-spine-target-var [] X = X
left-spine-target-var (both ∷ bs) X =
  left-spine-target-var bs (suc X)
left-spine-target-var (leftOnly ∷ bs) X =
  left-spine-target-var bs (suc X)
left-spine-target-var (rightOnly ∷ bs) X =
  left-spine-target-var bs X

left-spine-assm : OutputSpine → ImpAssm → ImpAssm
left-spine-assm [] a = a
left-spine-assm (both ∷ bs) a = left-spine-assm bs (⇑ᵢₐ a)
left-spine-assm (leftOnly ∷ bs) a = left-spine-assm bs (⇑ᵢₐ a)
left-spine-assm (rightOnly ∷ bs) a = left-spine-assm bs (⇑ᴸᵢₐ a)

left-spine-assm-star :
  ∀ bs X →
  left-spine-assm bs (X ˣ⊑★) ≡ left-spine-source-var bs X ˣ⊑★
left-spine-assm-star [] X = refl
left-spine-assm-star (both ∷ bs) X =
  left-spine-assm-star bs (suc X)
left-spine-assm-star (leftOnly ∷ bs) X =
  left-spine-assm-star bs (suc X)
left-spine-assm-star (rightOnly ∷ bs) X =
  left-spine-assm-star bs (suc X)

left-spine-assm-var :
  ∀ bs X Y →
  left-spine-assm bs (X ˣ⊑ˣ Y) ≡
    left-spine-source-var bs X ˣ⊑ˣ left-spine-target-var bs Y
left-spine-assm-var [] X Y = refl
left-spine-assm-var (both ∷ bs) X Y =
  left-spine-assm-var bs (suc X) (suc Y)
left-spine-assm-var (leftOnly ∷ bs) X Y =
  left-spine-assm-var bs (suc X) (suc Y)
left-spine-assm-var (rightOnly ∷ bs) X Y =
  left-spine-assm-var bs (suc X) Y

left-spine-binder-assm : OutBinder → ImpAssm
left-spine-binder-assm both = zero ˣ⊑ˣ zero
left-spine-binder-assm leftOnly = zero ˣ⊑ˣ zero
left-spine-binder-assm rightOnly = zero ˣ⊑★

⇑ᵢₐ-∈ :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᵢₐ a ∈ ⇑ᵢ Φ
⇑ᵢₐ-∈ {a = X ˣ⊑★} a∈ = ⇑ᵢ-★∈ a∈
⇑ᵢₐ-∈ {a = X ˣ⊑ˣ Y} a∈ = ⇑ᵢ-ˣ∈ a∈

⇑ᴸᵢₐ-∈ :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᴸᵢₐ a ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢₐ-∈ {a = X ˣ⊑★} a∈ = ⇑ᴸᵢ-★∈ a∈
⇑ᴸᵢₐ-∈ {a = X ˣ⊑ˣ Y} a∈ = ⇑ᴸᵢ-ˣ∈ a∈

left-spine-ctx-member :
  ∀ bs {Φ a} →
  a ∈ Φ →
  left-spine-assm bs a ∈ left-spine-ctx bs Φ
left-spine-ctx-member [] a∈ = a∈
left-spine-ctx-member (both ∷ bs) a∈ =
  left-spine-ctx-member bs (there (⇑ᵢₐ-∈ a∈))
left-spine-ctx-member (leftOnly ∷ bs) a∈ =
  left-spine-ctx-member bs (there (⇑ᵢₐ-∈ a∈))
left-spine-ctx-member (rightOnly ∷ bs) a∈ =
  left-spine-ctx-member bs (there (⇑ᴸᵢₐ-∈ a∈))

left-spine-ctx-emitted-member :
  ∀ b bs {Φ} →
  left-spine-assm bs (left-spine-binder-assm b) ∈
    left-spine-ctx (b ∷ bs) Φ
left-spine-ctx-emitted-member both bs =
  left-spine-ctx-member bs (here refl)
left-spine-ctx-emitted-member leftOnly bs =
  left-spine-ctx-member bs (here refl)
left-spine-ctx-emitted-member rightOnly bs =
  left-spine-ctx-member bs (here refl)

left-spine-ctx-emitted-between :
  ∀ outer b inner {Φ} →
  left-spine-assm inner (left-spine-binder-assm b) ∈
    left-spine-ctx (outer ++ (b ∷ inner)) Φ
left-spine-ctx-emitted-between outer b inner {Φ = Φ} =
  subst
    (λ Ψ → left-spine-assm inner (left-spine-binder-assm b) ∈ Ψ)
    (sym (left-spine-ctx-++ outer (b ∷ inner) Φ))
    (left-spine-ctx-emitted-member b inner)

foralls-used?-sound :
  ∀ {A} →
  foralls-used? A ≡ true →
  ForallsUsed A
foralls-used?-sound used≡ = used≡

WfTy-foralls-used :
  ∀ {Δ A} →
  WfTy Δ A →
  ForallsUsed A
WfTy-foralls-used (wfVar x<Δ) = refl
WfTy-foralls-used wfBase = refl
WfTy-foralls-used wf★ = refl
WfTy-foralls-used (wf⇒ hA hB)
    rewrite WfTy-foralls-used hA | WfTy-foralls-used hB = refl
WfTy-foralls-used (wf∀ {occ = occ} hA)
    rewrite occ | WfTy-foralls-used hA = refl

ForallsUsed-∀-occ :
  ∀ {A} →
  ForallsUsed (`∀ A) →
  occurs zero A ≡ true
ForallsUsed-∀-occ {A = A} used with occurs zero A | foralls-used? A
ForallsUsed-∀-occ used | true | true = refl
ForallsUsed-∀-occ () | true | false
ForallsUsed-∀-occ () | false | true
ForallsUsed-∀-occ () | false | false

ForallsUsed-∀-body :
  ∀ {A} →
  ForallsUsed (`∀ A) →
  ForallsUsed A
ForallsUsed-∀-body {A = A} used with occurs zero A | foralls-used? A
ForallsUsed-∀-body used | true | true = refl
ForallsUsed-∀-body () | true | false
ForallsUsed-∀-body () | false | true
ForallsUsed-∀-body () | false | false

+-suc-local : ∀ n Δ → n + suc Δ ≡ suc (n + Δ)
+-suc-local zero Δ = refl
+-suc-local (suc n) Δ = cong suc (+-suc-local n Δ)

split-∀-wf :
  ∀ {Δ A n A′ n∀A′} →
  WfTy Δ A →
  split-∀ A ≡ (n , A′ , n∀A′) →
  WfTy (n + Δ) A′
split-∀-wf {A = ＇ X} hA refl = hA
split-∀-wf {A = ‵ ι} hA refl = hA
split-∀-wf {A = ★} hA refl = hA
split-∀-wf {A = A ⇒ B} hA refl = hA
split-∀-wf {Δ = Δ} {A = `∀ A} (wf∀ hA) eq
    with split-∀ A in splitA≡
split-∀-wf {Δ = Δ} {A = `∀ A} (wf∀ hA) eq
    | n , A′ , n∀A′
    with eq
split-∀-wf {Δ = Δ} {A = `∀ A} (wf∀ hA) eq
    | n , A′ , n∀A′
    | refl =
  subst (λ Δ′ → WfTy Δ′ A′) (+-suc-local n Δ)
    (split-∀-wf hA splitA≡)

+-left-mono-< :
  ∀ m {X Δ} →
  X < Δ →
  m + X < m + Δ
+-left-mono-< zero X<Δ = X<Δ
+-left-mono-< (suc m) X<Δ = s<s (+-left-mono-< m X<Δ)

<-extend-right :
  ∀ {X n} m Δ →
  X < n →
  X < n + m + Δ
<-extend-right {zero} {suc n} m Δ z<s = z<s
<-extend-right {suc X} {suc n} m Δ (s<s X<n) =
  s<s (<-extend-right {X} {n} m Δ X<n)

drop-left-prefix-< :
  ∀ n m {X Δ} →
  X < n + Δ →
  ¬ (X < n) →
  n + m + (X ∸ n) < n + m + Δ
drop-left-prefix-< zero m X<Δ _ = +-left-mono-< m X<Δ
drop-left-prefix-< (suc n) m {zero} z<s ¬0<sucn =
  ⊥-elim (¬0<sucn z<s)
drop-left-prefix-< (suc n) m {suc X} (s<s X<n+Δ) ¬sucX<sucn =
  s<s (drop-left-prefix-< n m X<n+Δ λ X<n → ¬sucX<sucn (s<s X<n))

embed-left-rename-wf :
  ∀ {Δ n m} →
  TyRenameWf (n + Δ) (n + m + Δ) (embed-left-var n m)
embed-left-rename-wf {Δ} {n} {m} {X} X<n+Δ with X <? n
embed-left-rename-wf {Δ} {n} {m} {X} X<n+Δ | yes X<n =
  <-extend-right m Δ X<n
embed-left-rename-wf {Δ} {n} {m} {X} X<n+Δ | no ¬X<n =
  drop-left-prefix-< n m X<n+Δ ¬X<n

embed-left-wf :
  ∀ {Δ n m A} →
  WfTy (n + Δ) A →
  WfTy (n + m + Δ) (renameᵗ (embed-left-var n m) A)
embed-left-wf {Δ = Δ} {n = n} {m = m} {A = A} hA =
  renameᵗ-preserves-WfTy
    {Δ = n + Δ} {Δ′ = n + m + Δ}
    {A = A} {ρ = embed-left-var n m}
    hA (embed-left-rename-wf {Δ = Δ} {n = n} {m = m})

left-target-var : ℕ → ℕ → TyVar → TyVar
left-target-var n m X with X <? n | X <? (n + m)
... | yes _ | _ = X
... | no _ | yes _ = X
... | no _ | no _ = n + (X ∸ (n + m))

not-<-self+ : ∀ n k → ¬ (n + k < n)
not-<-self+ zero k ()
not-<-self+ (suc n) k (s<s n+k<n) = not-<-self+ n k n+k<n

not-<-double-prefix : ∀ n m k → ¬ (n + m + k < n)
not-<-double-prefix zero m k ()
not-<-double-prefix (suc n) m k (s<s n+m+k<n) =
  not-<-double-prefix n m k n+m+k<n

+-∸-cancel-left-local : ∀ n k → (n + k) ∸ n ≡ k
+-∸-cancel-left-local zero k = refl
+-∸-cancel-left-local (suc n) k = +-∸-cancel-left-local n k

+-∸-id-if-not< : ∀ n X → ¬ (X < n) → n + (X ∸ n) ≡ X
+-∸-id-if-not< zero X X≮0 = refl
+-∸-id-if-not< (suc n) zero 0≮sucn = ⊥-elim (0≮sucn z<s)
+-∸-id-if-not< (suc n) (suc X) sucX≮sucn =
  cong suc (+-∸-id-if-not< n X (λ X<n → sucX≮sucn (s<s X<n)))

left-target-var-embed-left :
  ∀ n m X →
  left-target-var n m (embed-left-var n m X) ≡ X
left-target-var-embed-left n m X with X <? n
left-target-var-embed-left n m X | yes X<n
    with X <? n | X <? (n + m)
left-target-var-embed-left n m X | yes X<n
    | yes _ | _ = refl
left-target-var-embed-left n m X | yes X<n
    | no X≮n | _ = ⊥-elim (X≮n X<n)
left-target-var-embed-left n m X | no X≮n
    with (n + m + (X ∸ n)) <? n
       | (n + m + (X ∸ n)) <? (n + m)
left-target-var-embed-left n m X | no X≮n
    | yes n+m+x∸n<n | _ =
  ⊥-elim (not-<-double-prefix n m (X ∸ n) n+m+x∸n<n)
left-target-var-embed-left n m X | no X≮n
    | no _ | yes n+m+x∸n<n+m =
  ⊥-elim (not-<-self+ (n + m) (X ∸ n) n+m+x∸n<n+m)
left-target-var-embed-left n m X | no X≮n
    | no _ | no _ =
  trans
    (cong (λ k → n + k) (+-∸-cancel-left-local (n + m) (X ∸ n)))
    (+-∸-id-if-not< n X X≮n)

right-target-var : ℕ → ℕ → TyVar → TyVar
right-target-var n m X with X <? n | X <? (n + m)
... | yes _ | _ = X
... | no _ | yes _ = X ∸ n
... | no _ | no _ = m + (X ∸ (n + m))

right-bound-embed-exact :
  ∀ n {Y m} →
  Y < m →
  n + Y < n + m
right-bound-embed-exact zero Y<m = Y<m
right-bound-embed-exact (suc n) Y<m =
  s<s (right-bound-embed-exact n Y<m)

right-target-var-embed-right :
  ∀ n m Y →
  right-target-var n m (embed-right-var n m Y) ≡ Y
right-target-var-embed-right n m Y with Y <? m
right-target-var-embed-right n m Y | yes Y<m
    with (n + Y) <? n | (n + Y) <? (n + m)
right-target-var-embed-right n m Y | yes Y<m
    | yes n+y<n | _ = ⊥-elim (not-<-self+ n Y n+y<n)
right-target-var-embed-right n m Y | yes Y<m
    | no _ | yes _ = +-∸-cancel-left-local n Y
right-target-var-embed-right n m Y | yes Y<m
    | no _ | no n+y≮n+m =
  ⊥-elim (n+y≮n+m (right-bound-embed-exact n Y<m))
right-target-var-embed-right n m Y | no Y≮m
    with (n + m + (Y ∸ m)) <? n
       | (n + m + (Y ∸ m)) <? (n + m)
right-target-var-embed-right n m Y | no Y≮m
    | yes n+m+y∸m<n | _ =
  ⊥-elim (not-<-double-prefix n m (Y ∸ m) n+m+y∸m<n)
right-target-var-embed-right n m Y | no Y≮m
    | no _ | yes n+m+y∸m<n+m =
  ⊥-elim (not-<-self+ (n + m) (Y ∸ m) n+m+y∸m<n+m)
right-target-var-embed-right n m Y | no Y≮m
    | no _ | no _ =
  trans
    (cong (λ k → m + k) (+-∸-cancel-left-local (n + m) (Y ∸ m)))
    (+-∸-id-if-not< m Y Y≮m)

<-+-right :
  ∀ {X m} Δ →
  X < m →
  X < m + Δ
<-+-right {m = zero} Δ ()
<-+-right {X = zero} {m = suc m} Δ z<s = z<s
<-+-right {X = suc X} {m = suc m} Δ (s<s X<m) =
  s<s (<-+-right Δ X<m)

right-bound-embed :
  ∀ n {Y m Δ} →
  Y < m →
  n + Y < n + m + Δ
right-bound-embed zero {Δ = Δ} Y<m = <-+-right Δ Y<m
right-bound-embed (suc n) Y<m = s<s (right-bound-embed n Y<m)

∸-lt-offset :
  ∀ {Y m Δ} →
  ¬ Y < m →
  Y < m + Δ →
  Y ∸ m < Δ
∸-lt-offset {m = zero} _ Y<Δ = Y<Δ
∸-lt-offset {Y = zero} {m = suc m} Y≮m _ = ⊥-elim (Y≮m z<s)
∸-lt-offset {Y = suc Y} {m = suc m} Y≮m (s<s Y<m+Δ) =
  ∸-lt-offset (λ Y<m → Y≮m (s<s Y<m)) Y<m+Δ

embed-right-rename-wf :
  ∀ {Δ n m} →
  TyRenameWf (m + Δ) (n + m + Δ) (embed-right-var n m)
embed-right-rename-wf {Δ} {n} {m} {Y} Y<m+Δ with Y <? m
embed-right-rename-wf {Δ} {n} {m} {Y} Y<m+Δ | yes Y<m =
  right-bound-embed n {Δ = Δ} Y<m
embed-right-rename-wf {Δ} {n} {m} {Y} Y<m+Δ | no Y≮m =
  +-left-mono-< (n + m) (∸-lt-offset Y≮m Y<m+Δ)

embed-right-wf :
  ∀ {Δ n m B} →
  WfTy (m + Δ) B →
  WfTy (n + m + Δ) (renameᵗ (embed-right-var n m) B)
embed-right-wf {Δ = Δ} {n = n} {m = m} {B = B} hB =
  renameᵗ-preserves-WfTy
    {Δ = m + Δ} {Δ′ = n + m + Δ}
    {A = B} {ρ = embed-right-var n m}
    hB (embed-right-rename-wf {Δ = Δ} {n = n} {m = m})

rename-assm² : Renameᵗ → Renameᵗ → ImpAssm → ImpAssm
rename-assm² ρ σ (X ˣ⊑★) = ρ X ˣ⊑★
rename-assm² ρ σ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ σ Y

rename-assm²-⇑ᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → rename-assm² ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ →
  rename-assm² (extᵗ ρ) (extᵗ σ) a ∈
    (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ
rename-assm²-⇑ᵢ h {a = zero ˣ⊑★} (here ())
rename-assm²-⇑ᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (h (un⇑ᵢ-★∈ a∈)))
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (here refl) = here refl
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (h (un⇑ᵢ-ˣ∈ a∈)))

rename-assm²-⇑ᴸᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → rename-assm² ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ →
  rename-assm² (extᵗ ρ) σ a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑★} (here refl) = here refl
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᴸᵢ-★∈ (h (un⇑ᴸᵢ-★∈ a∈)))
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (⇑ᴸᵢ-ˣ∈ (h (un⇑ᴸᵢ-ˣ∈ a∈)))

⊑-renameᵗ² :
  ∀ {Φ Ψ ρ σ A B} →
  (∀ {a} → a ∈ Φ → rename-assm² ρ σ a ∈ Ψ) →
  Φ ⊢ A ⊑ B →
  Ψ ⊢ renameᵗ ρ A ⊑ renameᵗ σ B
⊑-renameᵗ² h id★ = id★
⊑-renameᵗ² h (idˣ x∈) = idˣ (h x∈)
⊑-renameᵗ² h idι = idι
⊑-renameᵗ² h (p ↦ q) = ⊑-renameᵗ² h p ↦ ⊑-renameᵗ² h q
⊑-renameᵗ² {ρ = ρ} {σ = σ} h
    (∀ⁱ_ {A = A} {B = B} {occA = occA} {occB = occB} p) =
  ∀ⁱ_ {occA = trans (occurs-zero-rename-ext ρ A) occA}
      {occB = trans (occurs-zero-rename-ext σ B) occB}
      (⊑-renameᵗ² (rename-assm²-⇑ᵢ h) p)
⊑-renameᵗ² h (tag ι) = tag ι
⊑-renameᵗ² h (tag_⇛_ p q) =
  tag_⇛_ (⊑-renameᵗ² h p) (⊑-renameᵗ² h q)
⊑-renameᵗ² h (tagˣ x∈) = tagˣ (h x∈)
⊑-renameᵗ² {ρ = ρ} h
    (ν {A = A} {B = B} occA p) =
  ν (trans (occurs-zero-rename-ext ρ A) occA)
    (⊑-renameᵗ² (rename-assm²-⇑ᴸᵢ h) p)

CtxIncl : ImpCtx → ImpCtx → Set
CtxIncl Φ Ψ = ∀ {a} → a ∈ Φ → a ∈ Ψ

CAssmIncl : List CAssm → List CAssm → Set
CAssmIncl Γ Γ′ = ∀ {a} → a ∈ Γ → a ∈ Γ′

⇑ᵢ-incl :
  ∀ {Φ Ψ a} →
  CtxIncl Φ Ψ →
  a ∈ ⇑ᵢ Φ →
  a ∈ ⇑ᵢ Ψ
⇑ᵢ-incl {a = zero ˣ⊑★} incl a∈ =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
⇑ᵢ-incl {a = suc X ˣ⊑★} incl a∈ =
  ⇑ᵢ-★∈ (incl (un⇑ᵢ-★∈ a∈))
⇑ᵢ-incl {a = zero ˣ⊑ˣ Y} incl a∈ =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
⇑ᵢ-incl {a = suc X ˣ⊑ˣ zero} incl a∈ =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
⇑ᵢ-incl {a = suc X ˣ⊑ˣ suc Y} incl a∈ =
  ⇑ᵢ-ˣ∈ (incl (un⇑ᵢ-ˣ∈ a∈))

⇑ᴸᵢ-incl :
  ∀ {Φ Ψ a} →
  CtxIncl Φ Ψ →
  a ∈ ⇑ᴸᵢ Φ →
  a ∈ ⇑ᴸᵢ Ψ
⇑ᴸᵢ-incl {a = zero ˣ⊑★} incl a∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
⇑ᴸᵢ-incl {a = suc X ˣ⊑★} incl a∈ =
  ⇑ᴸᵢ-★∈ (incl (un⇑ᴸᵢ-★∈ a∈))
⇑ᴸᵢ-incl {a = zero ˣ⊑ˣ Y} incl a∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
⇑ᴸᵢ-incl {a = suc X ˣ⊑ˣ Y} incl a∈ =
  ⇑ᴸᵢ-ˣ∈ (incl (un⇑ᴸᵢ-ˣ∈ a∈))

left-spine-ctx-incl :
  ∀ bs {Φ Ψ} →
  CtxIncl Φ Ψ →
  CtxIncl (left-spine-ctx bs Φ) (left-spine-ctx bs Ψ)
left-spine-ctx-incl [] incl = incl
left-spine-ctx-incl (both ∷ bs) {Φ = Φ} {Ψ = Ψ} incl =
  left-spine-ctx-incl bs incl′
  where
    incl′ :
      CtxIncl ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
              ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
    incl′ (here refl) = here refl
    incl′ (there a∈) = there (⇑ᵢ-incl incl a∈)
left-spine-ctx-incl (leftOnly ∷ bs) {Φ = Φ} {Ψ = Ψ} incl =
  left-spine-ctx-incl bs incl′
  where
    incl′ :
      CtxIncl ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
              ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
    incl′ (here refl) = here refl
    incl′ (there a∈) = there (⇑ᵢ-incl incl a∈)
left-spine-ctx-incl (rightOnly ∷ bs) {Φ = Φ} {Ψ = Ψ} incl =
  left-spine-ctx-incl bs incl′
  where
    incl′ : CtxIncl ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
                    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    incl′ (here refl) = here refl
    incl′ (there a∈) = there (⇑ᴸᵢ-incl incl a∈)

⊑-mono :
  ∀ {Φ Ψ A B} →
  CtxIncl Φ Ψ →
  Φ ⊢ A ⊑ B →
  Ψ ⊢ A ⊑ B
⊑-mono incl id★ = id★
⊑-mono incl (idˣ x∈) = idˣ (incl x∈)
⊑-mono incl idι = idι
⊑-mono incl (p ↦ q) = ⊑-mono incl p ↦ ⊑-mono incl q
⊑-mono {Φ = Φ} {Ψ = Ψ} incl
    (∀ⁱ_ {A = A} {B = B} {occA = occA} {occB = occB} p) =
  ∀ⁱ_ {A = A} {B = B} {occA = occA} {occB = occB}
    (⊑-mono
      {Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ}
      {Ψ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ}
      incl′ p)
  where
    incl′ : CtxIncl ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
                    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
    incl′ (here refl) = here refl
    incl′ (there a∈) = there (⇑ᵢ-incl incl a∈)
⊑-mono incl (tag ι) = tag ι
⊑-mono incl (tag_⇛_ p q) = tag_⇛_ (⊑-mono incl p) (⊑-mono incl q)
⊑-mono incl (tagˣ x∈) = tagˣ (incl x∈)
⊑-mono {Φ = Φ} {Ψ = Ψ} incl (ν occ p) =
  ν occ
    (⊑-mono
      {Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ}
      {Ψ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ}
      incl′ p)
  where
    incl′ : CtxIncl ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
                    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    incl′ (here refl) = here refl
    incl′ (there a∈) = there (⇑ᴸᵢ-incl incl a∈)

assm-left-member :
  ∀ {Γ a} →
  a ∈ Γ →
  assm-left-assm a ∈ assm-left Γ
assm-left-member {Γ = []} ()
assm-left-member {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
assm-left-member {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
assm-left-member {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
assm-left-member {Γ = (_ ~ᶜ _) ∷ Γ} (there a∈) =
  there (assm-left-member a∈)
assm-left-member {Γ = (_ ~ᶜ★) ∷ Γ} (there a∈) =
  there (assm-left-member a∈)
assm-left-member {Γ = (★~ᶜ _) ∷ Γ} (there a∈) =
  there (assm-left-member a∈)

left-spine-ctx-assm-left-member :
  ∀ bs {Γ a} →
  a ∈ Γ →
  left-spine-assm bs (assm-left-assm a) ∈
    left-spine-ctx bs (assm-left Γ)
left-spine-ctx-assm-left-member bs a∈ =
  left-spine-ctx-member bs (assm-left-member a∈)

assm-right-member :
  ∀ {Γ a} →
  a ∈ Γ →
  assm-right-assm a ∈ assm-right Γ
assm-right-member {Γ = []} ()
assm-right-member {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
assm-right-member {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
assm-right-member {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
assm-right-member {Γ = (_ ~ᶜ _) ∷ Γ} (there a∈) =
  there (assm-right-member a∈)
assm-right-member {Γ = (_ ~ᶜ★) ∷ Γ} (there a∈) =
  there (assm-right-member a∈)
assm-right-member {Γ = (★~ᶜ _) ∷ Γ} (there a∈) =
  there (assm-right-member a∈)

assm-left-incl :
  ∀ {Γ Γ′} →
  CAssmIncl Γ Γ′ →
  CtxIncl (assm-left Γ) (assm-left Γ′)
assm-left-incl {Γ = []} incl ()
assm-left-incl {Γ = (_ ~ᶜ _) ∷ Γ} incl (here refl) =
  assm-left-member (incl (here refl))
assm-left-incl {Γ = (_ ~ᶜ★) ∷ Γ} incl (here refl) =
  assm-left-member (incl (here refl))
assm-left-incl {Γ = (★~ᶜ _) ∷ Γ} incl (here refl) =
  assm-left-member (incl (here refl))
assm-left-incl {Γ = _ ∷ Γ} incl (there a∈) =
  assm-left-incl (λ b∈ → incl (there b∈)) a∈

assm-right-incl :
  ∀ {Γ Γ′} →
  CAssmIncl Γ Γ′ →
  CtxIncl (assm-right Γ) (assm-right Γ′)
assm-right-incl {Γ = []} incl ()
assm-right-incl {Γ = (_ ~ᶜ _) ∷ Γ} incl (here refl) =
  assm-right-member (incl (here refl))
assm-right-incl {Γ = (_ ~ᶜ★) ∷ Γ} incl (here refl) =
  assm-right-member (incl (here refl))
assm-right-incl {Γ = (★~ᶜ _) ∷ Γ} incl (here refl) =
  assm-right-member (incl (here refl))
assm-right-incl {Γ = _ ∷ Γ} incl (there a∈) =
  assm-right-incl (λ b∈ → incl (there b∈)) a∈

same-assm?-sound :
  ∀ {a b} →
  same-assm? a b ≡ true →
  a ≡ b
same-assm?-sound {a = X ~ᶜ★} {b = X′ ~ᶜ★} eq
    with X ≟ X′
same-assm?-sound {a = X ~ᶜ★} {b = .X ~ᶜ★} eq | yes refl = refl
same-assm?-sound {a = X ~ᶜ★} {b = X′ ~ᶜ★} () | no _
same-assm?-sound {a = X ~ᶜ★} {b = ★~ᶜ Y′} ()
same-assm?-sound {a = X ~ᶜ★} {b = X′ ~ᶜ Y′} ()
same-assm?-sound {a = ★~ᶜ Y} {b = X′ ~ᶜ★} ()
same-assm?-sound {a = ★~ᶜ Y} {b = ★~ᶜ Y′} eq
    with Y ≟ Y′
same-assm?-sound {a = ★~ᶜ Y} {b = ★~ᶜ .Y} eq | yes refl = refl
same-assm?-sound {a = ★~ᶜ Y} {b = ★~ᶜ Y′} () | no _
same-assm?-sound {a = ★~ᶜ Y} {b = X′ ~ᶜ Y′} ()
same-assm?-sound {a = X ~ᶜ Y} {b = X′ ~ᶜ★} ()
same-assm?-sound {a = X ~ᶜ Y} {b = ★~ᶜ Y′} ()
same-assm?-sound {a = X ~ᶜ Y} {b = X′ ~ᶜ Y′} eq
    with X ≟ X′ | Y ≟ Y′
same-assm?-sound {a = X ~ᶜ Y} {b = .X ~ᶜ .Y} eq
    | yes refl | yes refl = refl
same-assm?-sound {a = X ~ᶜ Y} {b = X′ ~ᶜ Y′} ()
    | yes _ | no _
same-assm?-sound {a = X ~ᶜ Y} {b = X′ ~ᶜ Y′} ()
    | no _ | yes _
same-assm?-sound {a = X ~ᶜ Y} {b = X′ ~ᶜ Y′} ()
    | no _ | no _

insert-assm-includes-new :
  ∀ {a Γ Γ′} →
  insert-assm a Γ ≡ just Γ′ →
  a ∈ Γ′
insert-assm-includes-new {Γ = []} refl = here refl
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} eq
    with same-assm? a b in same≡ | clash? a b
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} refl
    | true | c =
  subst (λ d → d ∈ b ∷ Γ) (sym (same-assm?-sound same≡))
    (here refl)
insert-assm-includes-new {Γ = b ∷ Γ} () | false | true
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} eq
    | false | false
    with insert-assm a Γ in ins≡
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} ()
    | false | false | nothing
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} eq
    | false | false | just Γ′
    with eq
insert-assm-includes-new {a = a} {Γ = b ∷ Γ} refl
    | false | false | just Γ′ | refl =
  there (insert-assm-includes-new {a = a} {Γ = Γ} {Γ′ = Γ′} ins≡)

insert-assm-preserves :
  ∀ {a Γ Γ′} →
  insert-assm a Γ ≡ just Γ′ →
  CAssmIncl Γ Γ′
insert-assm-preserves {Γ = []} eq ()
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq old∈
    with same-assm? a b | clash? a b
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq old∈
    | true | c
    with eq
insert-assm-preserves {a = a} {Γ = b ∷ Γ} refl old∈
    | true | c | refl = old∈
insert-assm-preserves {Γ = b ∷ Γ} () old∈ | false | true
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq (here refl)
    | false | false
    with insert-assm a Γ
insert-assm-preserves {a = a} {Γ = b ∷ Γ} () (here refl)
    | false | false | nothing
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq (here refl)
    | false | false | just Γ′
    with eq
insert-assm-preserves {a = a} {Γ = b ∷ Γ} refl (here refl)
    | false | false | just Γ′ | refl = here refl
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq (there old∈)
    | false | false
    with insert-assm a Γ in ins≡
insert-assm-preserves {a = a} {Γ = b ∷ Γ} () (there old∈)
    | false | false | nothing
insert-assm-preserves {a = a} {Γ = b ∷ Γ} eq (there old∈)
    | false | false | just Γ′
    with eq
insert-assm-preserves {a = a} {Γ = b ∷ Γ} refl (there old∈)
    | false | false | just Γ′ | refl =
  there (insert-assm-preserves {a = a} {Γ = Γ} {Γ′ = Γ′} ins≡ old∈)

merge-assms-left :
  ∀ {Γ₁ Γ₂ Γ} →
  merge-assms Γ₁ Γ₂ ≡ just Γ →
  CAssmIncl Γ₁ Γ
merge-assms-left {Γ₁ = []} eq ()
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} {Γ = Γ} eq (here refl)
    with merge-assms Γ₁ Γ₂ in merge≡
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} {Γ = Γ} () (here refl)
    | nothing
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} {Γ = Γ} eq (here refl)
    | just Γ″ =
  insert-assm-includes-new {a = a} {Γ = Γ″} {Γ′ = Γ} eq
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} eq (there a∈)
    with merge-assms Γ₁ Γ₂ in merge≡
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} () (there a∈)
    | nothing
merge-assms-left {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} eq (there a∈)
    | just Γ″ =
  insert-assm-preserves {a = a} {Γ = Γ″} eq
    (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ″} merge≡ a∈)

merge-assms-right :
  ∀ {Γ₁ Γ₂ Γ} →
  merge-assms Γ₁ Γ₂ ≡ just Γ →
  CAssmIncl Γ₂ Γ
merge-assms-right {Γ₁ = []} refl a∈ = a∈
merge-assms-right {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} eq a∈
    with merge-assms Γ₁ Γ₂ in merge≡
merge-assms-right {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} () a∈
    | nothing
merge-assms-right {Γ₁ = a ∷ Γ₁} {Γ₂ = Γ₂} eq a∈
    | just Γ″ =
  insert-assm-preserves {a = a} {Γ = Γ″} eq
    (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ″} merge≡ a∈)

normalize-assms-clash-check-includes :
  ∀ {n m Γ₀ Γ a} →
  normalize-assms-clash-check n m Γ₀ ≡ just Γ →
  a ∈ Γ₀ →
  normalize-assm n m Γ₀ a ∈ Γ
normalize-assms-clash-check-includes {Γ₀ = []} eq ()
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = a ∷ Γ₀} eq (here refl)
    with normalize-assms-clash-check n m Γ₀
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = a ∷ Γ₀} () (here refl) | nothing
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = a ∷ Γ₀} eq (here refl) | just Γ′ =
  insert-assm-includes-new
    {a = normalize-assm n m (a ∷ Γ₀) a} {Γ = Γ′} eq
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} {a = b} eq (there b∈)
    with normalize-assms-clash-check n m Γ₀ in chk≡
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} () (there b∈) | nothing
normalize-assms-clash-check-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} {a = b} eq (there b∈) | just Γ′ =
  insert-assm-preserves
    {a = normalize-assm n m (h ∷ Γ₀) h} {Γ = Γ′} eq
    (subst
      (λ a′ → a′ ∈ Γ′)
      (sym (normalize-assm-ctx-irrelevant n m (h ∷ Γ₀) Γ₀ b))
      (normalize-assms-clash-check-includes
        {n = n} {m = m} {Γ₀ = Γ₀} chk≡ b∈))

normalize-assms-residual-includes :
  ∀ {n m Γ₀ Γ a} →
  normalize-assms-residual n m Γ₀ ≡ just Γ →
  discharged-assm? n m a ≡ false →
  a ∈ Γ₀ →
  normalize-assm n m Γ₀ a ∈ Γ
normalize-assms-residual-includes {Γ₀ = []} eq notDis ()
normalize-assms-residual-includes {n = n} {m = m}
    {Γ₀ = a ∷ Γ₀} eq notDis (here refl)
    with normalize-assms-residual n m Γ₀ | discharged-assm? n m a
normalize-assms-residual-includes {Γ₀ = a ∷ Γ₀} ()
    notDis (here refl) | nothing | _
normalize-assms-residual-includes {Γ₀ = a ∷ Γ₀} eq
    () (here refl) | just Γ′ | true
normalize-assms-residual-includes {n = n} {m = m}
    {Γ₀ = a ∷ Γ₀} eq notDis (here refl) | just Γ′ | false =
  insert-assm-includes-new
    {a = normalize-assm n m (a ∷ Γ₀) a} {Γ = Γ′} eq
normalize-assms-residual-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} {a = b} eq notDis (there b∈)
    with normalize-assms-residual n m Γ₀ in norm≡
       | discharged-assm? n m h
normalize-assms-residual-includes {Γ₀ = h ∷ Γ₀} ()
    notDis (there b∈) | nothing | _
normalize-assms-residual-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} {Γ = Γ} {a = b} eq notDis (there b∈)
    | just Γ′ | true =
    helper eq
  where
    helper :
      just Γ′ ≡ just Γ →
      normalize-assm n m (h ∷ Γ₀) b ∈ Γ
    helper refl =
      subst
        (λ a′ → a′ ∈ Γ′)
        (sym (normalize-assm-ctx-irrelevant n m (h ∷ Γ₀) Γ₀ b))
        (normalize-assms-residual-includes
          {n = n} {m = m} {Γ₀ = Γ₀} norm≡ notDis b∈)
normalize-assms-residual-includes {n = n} {m = m}
    {Γ₀ = h ∷ Γ₀} {a = b} eq notDis (there b∈) | just Γ′ | false
    with normalize-assm n m (h ∷ Γ₀) h
... | a′ =
  insert-assm-preserves {a = a′} {Γ = Γ′} eq
    (subst
      (λ b′ → b′ ∈ Γ′)
      (sym (normalize-assm-ctx-irrelevant n m (h ∷ Γ₀) Γ₀ b))
      (normalize-assms-residual-includes
        {n = n} {m = m} {Γ₀ = Γ₀} norm≡ notDis b∈))

normalize-assms-includes-residual :
  ∀ {n m Γ₀ Γ a} →
  normalize-assms n m Γ₀ ≡ just Γ →
  discharged-assm? n m a ≡ false →
  a ∈ Γ₀ →
  normalize-assm n m Γ₀ a ∈ Γ
normalize-assms-includes-residual {n = n} {m = m} {Γ₀ = Γ₀}
    norm≡ notDis a∈
    with normalize-assms-clash-check n m Γ₀
normalize-assms-includes-residual {Γ₀ = Γ₀} () notDis a∈
    | nothing
normalize-assms-includes-residual {n = n} {m = m} {Γ₀ = Γ₀}
    norm≡ notDis a∈ | just _ =
  normalize-assms-residual-includes norm≡ notDis a∈

normalize-assms-for :
  ℕ → ℕ → List CAssm → List CAssm → List CAssm
normalize-assms-for n m Γ₀ [] = []
normalize-assms-for n m Γ₀ (a ∷ Γ) =
  normalize-assm n m Γ₀ a ∷ normalize-assms-for n m Γ₀ Γ

normalize-left-assms-for :
  ℕ → ℕ → List CAssm → List CAssm → ImpCtx
normalize-left-assms-for n m Γ₀ [] = []
normalize-left-assms-for n m Γ₀ (a ∷ Γ) =
  rename-assm² (normalize-var n m Γ₀) (left-target-var n m)
    (assm-left-assm a)
  ∷ normalize-left-assms-for n m Γ₀ Γ

normalize-right-assms-for :
  ℕ → ℕ → List CAssm → List CAssm → ImpCtx
normalize-right-assms-for n m Γ₀ [] = []
normalize-right-assms-for n m Γ₀ (a ∷ Γ) =
  rename-assm² (normalize-var n m Γ₀) (right-target-var n m)
    (assm-right-assm a)
  ∷ normalize-right-assms-for n m Γ₀ Γ

spine-left : ℕ → ℕ → List CAssm → List CAssm → ImpCtx
spine-left n m Γ₀ Γ = normalize-left-assms-for n m Γ₀ Γ₀

spine-right : ℕ → ℕ → List CAssm → List CAssm → ImpCtx
spine-right n m Γ₀ Γ = normalize-right-assms-for n m Γ₀ Γ₀

normalize-left-incl :
  ∀ {n m Γ₀ Γ a} →
  a ∈ assm-left Γ →
  rename-assm² (normalize-var n m Γ₀) (left-target-var n m) a ∈
    normalize-left-assms-for n m Γ₀ Γ
normalize-left-incl {Γ = []} ()
normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = a ∷ Γ} (there a∈) =
  there (normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀}
           {Γ = Γ} a∈)

normalize-left-assms-for-member :
  ∀ {n m Γ₀ Γ a} →
  a ∈ normalize-left-assms-for n m Γ₀ Γ →
  Σ[ b ∈ CAssm ]
    (b ∈ Γ ×
     a ≡ rename-assm² (normalize-var n m Γ₀) (left-target-var n m)
           (assm-left-assm b))
normalize-left-assms-for-member {Γ = []} ()
normalize-left-assms-for-member {Γ = b ∷ Γ} (here refl) =
  b , here refl , refl
normalize-left-assms-for-member {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = b ∷ Γ} (there a∈)
    with normalize-left-assms-for-member {n = n} {m = m}
           {Γ₀ = Γ₀} {Γ = Γ} a∈
normalize-left-assms-for-member {Γ = b ∷ Γ} (there a∈)
    | c , c∈ , eq =
  c , there c∈ , eq

normalize-right-incl :
  ∀ {n m Γ₀ Γ a} →
  a ∈ assm-right Γ →
  rename-assm² (normalize-var n m Γ₀) (right-target-var n m) a ∈
    normalize-right-assms-for n m Γ₀ Γ
normalize-right-incl {Γ = []} ()
normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = a ∷ Γ} (there a∈) =
  there (normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀}
           {Γ = Γ} a∈)

normalize-lower-spine :
  ∀ {n m Γ₀ Γ C A B} →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  assm-left Γ₀ ⊢ C ⊑ A × assm-right Γ₀ ⊢ C ⊑ B →
  spine-left n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C
                         ⊑ renameᵗ (left-target-var n m) A
    ×
  spine-right n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C
                          ⊑ renameᵗ (right-target-var n m) B
normalize-lower-spine {n = n} {m = m} {Γ₀ = Γ₀}
    noEsc≡ order≡ norm≡ (C⊑A , C⊑B) =
  ( ⊑-renameᵗ²
      (normalize-left-incl {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ₀})
      C⊑A
  , ⊑-renameᵗ²
      (normalize-right-incl {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ₀})
      C⊑B
  )

normalized-type : ℕ → ℕ → List CAssm → Ty → Ty
normalized-type n m Γ₀ A = renameᵗ (normalize-var n m Γ₀) A

left-normalized-target : ℕ → ℕ → List CAssm → Ty → Ty
left-normalized-target n m Γ₀ A′ =
  renameᵗ (left-target-var n m) (renameᵗ (embed-left-var n m) A′)

left-normalized-target-cancel :
  ∀ n m Γ₀ A →
  left-normalized-target n m Γ₀ A ≡ A
left-normalized-target-cancel n m Γ₀ A =
  trans
    (renameᵗ-compose (embed-left-var n m) (left-target-var n m) A)
    (trans
      (rename-cong (left-target-var-embed-left n m) A)
      (renameᵗ-id A))

right-normalized-target : ℕ → ℕ → List CAssm → Ty → Ty
right-normalized-target n m Γ₀ B′ =
  renameᵗ (right-target-var n m) (renameᵗ (embed-right-var n m) B′)

right-normalized-target-cancel :
  ∀ n m Γ₀ B →
  right-normalized-target n m Γ₀ B ≡ B
right-normalized-target-cancel n m Γ₀ B =
  trans
    (renameᵗ-compose (embed-right-var n m) (right-target-var n m) B)
    (trans
      (rename-cong (right-target-var-embed-right n m) B)
      (renameᵗ-id B))

rightOnlys-then : ℕ → OutputSpine → OutputSpine
rightOnlys-then zero bs = bs
rightOnlys-then (suc n) bs = rightOnly ∷ rightOnlys-then n bs

rightOnlys-then-snoc :
  ∀ k →
  rightOnlys-then k [] ++ (rightOnly ∷ []) ≡
  rightOnlys-then (suc k) []
rightOnlys-then-snoc zero = refl
rightOnlys-then-snoc (suc k) =
  cong (λ bs → rightOnly ∷ bs) (rightOnlys-then-snoc k)

reverse-local-rightOnlys-then-cons :
  ∀ k b bs →
  reverse-local (rightOnlys-then k (b ∷ bs)) ≡
  reverse-local bs ++ (b ∷ rightOnlys-then k [])
reverse-local-rightOnlys-then-cons zero b bs = refl
reverse-local-rightOnlys-then-cons (suc k) b bs =
  trans
    (cong (λ xs → xs ++ (rightOnly ∷ []))
      (reverse-local-rightOnlys-then-cons k b bs))
    (trans
      (++-assoc-local (reverse-local bs)
        (b ∷ rightOnlys-then k []) (rightOnly ∷ []))
      (cong (λ xs → reverse-local bs ++ (b ∷ xs))
        (rightOnlys-then-snoc k)))

left-spine-target-var-rightOnlys-then :
  ∀ k bs X →
  left-spine-target-var (rightOnlys-then k bs) X ≡
    left-spine-target-var bs X
left-spine-target-var-rightOnlys-then zero bs X = refl
left-spine-target-var-rightOnlys-then (suc k) bs X =
  left-spine-target-var-rightOnlys-then k bs X

rightOnlys-then-head-emitted-member :
  ∀ k bs {Φ} →
  left-spine-assm (rightOnlys-then k bs) (zero ˣ⊑★) ∈
    left-spine-ctx (rightOnlys-then (suc k) bs) Φ
rightOnlys-then-head-emitted-member k bs =
  left-spine-ctx-emitted-member rightOnly (rightOnlys-then k bs)

rightOnlys-then-tail-emitted-member :
  ∀ k b bs {Φ} →
  left-spine-assm bs (left-spine-binder-assm b) ∈
    left-spine-ctx (rightOnlys-then k (b ∷ bs)) Φ
rightOnlys-then-tail-emitted-member zero b bs =
  left-spine-ctx-emitted-member b bs
rightOnlys-then-tail-emitted-member (suc k) b bs =
  rightOnlys-then-tail-emitted-member k b bs

rightOnlys-then-length :
  ∀ k bs →
  length (rightOnlys-then k bs) ≡ rightOnlys-count k (length bs)
rightOnlys-then-length zero bs = refl
rightOnlys-then-length (suc k) bs =
  cong suc (rightOnlys-then-length k bs)

left-binder-out : ℕ → ℕ → List CAssm → TyVar → OutBinder
left-binder-out n m Γ X with find-bound-right-for-left n m X Γ
... | just Y = both
... | nothing = leftOnly

left-output-spine-from :
  ℕ → ℕ → List CAssm → ℕ → TyVar → ℕ → OutputSpine
left-output-spine-from n m Γ zero X emitted =
  rightOnlys-then (unmatched-right-before n m Γ ∸ emitted) []
left-output-spine-from n m Γ (suc fuel) X emitted
    with unmatched-rights-before-left n m Γ X
... | before =
  rightOnlys-then (before ∸ emitted)
    (left-binder-out n m Γ X ∷
     left-output-spine-from n m Γ fuel (suc X) before)

left-output-spine : ℕ → ℕ → List CAssm → List CAssm → OutputSpine
left-output-spine n m Γ₀ Γ =
  reverse-local (left-output-spine-from n m Γ₀ n zero zero)

left-output-spine-from-left-binder-member :
  ∀ n m Γ fuel X emitted {Φ} →
  left-spine-assm
    (left-output-spine-from n m Γ fuel (suc X)
      (unmatched-rights-before-left n m Γ X))
    (left-spine-binder-assm (left-binder-out n m Γ X)) ∈
  left-spine-ctx
    (left-output-spine-from n m Γ (suc fuel) X emitted) Φ
left-output-spine-from-left-binder-member n m Γ fuel X emitted
    with unmatched-rights-before-left n m Γ X
... | before =
  rightOnlys-then-tail-emitted-member
    (before ∸ emitted)
    (left-binder-out n m Γ X)
    (left-output-spine-from n m Γ fuel (suc X) before)

left-output-spine-from-left-binder-member-reverse :
  ∀ n m Γ fuel X emitted {Φ} →
  left-spine-assm (rightOnlys-then
    (unmatched-rights-before-left n m Γ X ∸ emitted) [])
    (left-spine-binder-assm (left-binder-out n m Γ X)) ∈
  left-spine-ctx
    (reverse-local (left-output-spine-from n m Γ (suc fuel) X emitted)) Φ
left-output-spine-from-left-binder-member-reverse n m Γ fuel X emitted
    with unmatched-rights-before-left n m Γ X
... | before =
  subst
    (λ bs →
      left-spine-assm (rightOnlys-then (before ∸ emitted) [])
        (left-spine-binder-assm (left-binder-out n m Γ X)) ∈
      left-spine-ctx bs _)
    (sym
      (reverse-local-rightOnlys-then-cons
        (before ∸ emitted)
        (left-binder-out n m Γ X)
        (left-output-spine-from n m Γ fuel (suc X) before)))
    (left-spine-ctx-emitted-between
      (reverse-local (left-output-spine-from n m Γ fuel (suc X) before))
      (left-binder-out n m Γ X)
      (rightOnlys-then (before ∸ emitted) []))

left-output-spine-residual-member :
  ∀ {n m Γ₀ Γ a} →
  a ∈ Γ →
  left-spine-assm (left-output-spine n m Γ₀ Γ) (assm-left-assm a) ∈
    left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ)
left-output-spine-residual-member {n = n} {m = m} {Γ₀ = Γ₀}
    {Γ = Γ} a∈ =
  left-spine-ctx-assm-left-member (left-output-spine n m Γ₀ Γ) a∈

left-output-spine-from-length :
  ∀ n m Γ fuel X emitted →
  length (left-output-spine-from n m Γ fuel X emitted) ≡
  left-output-spine-count-from n m Γ fuel X emitted
left-output-spine-from-length n m Γ zero X emitted =
  rightOnlys-then-length (unmatched-right-before n m Γ ∸ emitted) []
left-output-spine-from-length n m Γ (suc fuel) X emitted
    with unmatched-rights-before-left n m Γ X
left-output-spine-from-length n m Γ (suc fuel) X emitted
    | before =
  trans
    (rightOnlys-then-length
      (before ∸ emitted)
      (left-binder-out n m Γ X ∷
       left-output-spine-from n m Γ fuel (suc X) before))
    (cong (rightOnlys-count (before ∸ emitted))
      (cong suc
        (left-output-spine-from-length n m Γ fuel (suc X) before)))

wrap-left-target-rightOnlys-then :
  ∀ k bs A →
  wrap-left-target (rightOnlys-then k bs) A ≡ wrap-left-target bs A
wrap-left-target-rightOnlys-then zero bs A = refl
wrap-left-target-rightOnlys-then (suc k) bs A =
  wrap-left-target-rightOnlys-then k bs A

wrap-left-target-spine-from :
  ∀ n m Γ fuel X emitted A →
  wrap-left-target (left-output-spine-from n m Γ fuel X emitted) A ≡
  add∀ fuel A
wrap-left-target-spine-from n m Γ zero X emitted A =
  wrap-left-target-rightOnlys-then
    (unmatched-right-before n m Γ ∸ emitted) [] A
wrap-left-target-spine-from n m Γ (suc fuel) X emitted A
    with unmatched-rights-before-left n m Γ X
wrap-left-target-spine-from n m Γ (suc fuel) X emitted A
    | before
    with find-bound-right-for-left n m X Γ
wrap-left-target-spine-from n m Γ (suc fuel) X emitted A
    | before | just Y =
  trans
    (wrap-left-target-rightOnlys-then
      (before ∸ emitted)
      (both ∷ left-output-spine-from n m Γ fuel (suc X) before) A)
    (cong `∀ (wrap-left-target-spine-from n m Γ fuel (suc X) before A))
wrap-left-target-spine-from n m Γ (suc fuel) X emitted A
    | before | nothing =
  trans
    (wrap-left-target-rightOnlys-then
      (before ∸ emitted)
      (leftOnly ∷ left-output-spine-from n m Γ fuel (suc X) before) A)
    (cong `∀ (wrap-left-target-spine-from n m Γ fuel (suc X) before A))

wrap-left-target-left-output-spine :
  ∀ n m Γ₀ Γ A →
  wrap-left-target (left-output-spine n m Γ₀ Γ) A ≡ add∀ n A
wrap-left-target-left-output-spine n m Γ₀ Γ A =
  trans
    (wrap-left-target-reverse
      (left-output-spine-from n m Γ₀ n zero zero) A)
    (wrap-left-target-spine-from n m Γ₀ n zero zero A)

left-output-spine-length :
  ∀ {n m Γ₀ Γ} →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  length (left-output-spine n m Γ₀ Γ) ≡ mlb-∀-count n m Γ₀
left-output-spine-length {n = n} {m = m} {Γ₀ = Γ₀} noEsc≡ order≡ norm≡ =
  trans
    (length-reverse-local (left-output-spine-from n m Γ₀ n zero zero))
    (left-output-spine-from-length n m Γ₀ n zero zero)

postulate

  left-spine-context-contains-left-raw :
    ∀ {n m Γ₀ Γ a} →
    no-escaping-assms? n m Γ₀ ≡ true →
    bound-var-var-order-ok-list? n m Γ₀ ≡ true →
    normalize-assms n m Γ₀ ≡ just Γ →
    a ∈ Γ₀ →
    rename-assm² (normalize-var n m Γ₀) (left-target-var n m)
      (assm-left-assm a) ∈
    left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ)

left-spine-context-sound :
  ∀ {n m Γ₀ Γ} →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  CtxIncl (spine-left n m Γ₀ Γ)
          (left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ))
left-spine-context-sound {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ}
    noEsc≡ order≡ norm≡ {a = a} a∈ =
  subst
    (λ b → b ∈ left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ))
    (sym eq)
    (left-spine-context-contains-left-raw
      {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ} noEsc≡ order≡ norm≡ raw∈)
  where
    raw :
      Σ[ b ∈ CAssm ]
        (b ∈ Γ₀ ×
         a ≡ rename-assm² (normalize-var n m Γ₀) (left-target-var n m)
               (assm-left-assm b))
    raw = normalize-left-assms-for-member
            {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ₀} a∈

    raw∈ : proj₁ raw ∈ Γ₀
    raw∈ = proj₁ (proj₂ raw)

    eq :
      a ≡ rename-assm² (normalize-var n m Γ₀) (left-target-var n m)
            (assm-left-assm (proj₁ raw))
    eq = proj₂ (proj₂ raw)

left-spine-target-sound :
  ∀ {A n m A′ n∀A′ Γ₀ Γ} →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  split-∀ A ≡ (n , A′ , n∀A′) →
  wrap-left-target (left-output-spine n m Γ₀ Γ) A′ ≡ A
left-spine-target-sound {n = n} {m = m} {A′ = A′}
    {Γ₀ = Γ₀} {Γ = Γ} noEsc≡ order≡ norm≡ splitA≡ =
  trans (wrap-left-target-left-output-spine n m Γ₀ Γ A′)
        (sym (split-∀-rebuild splitA≡))

wrap-left-spine :
  ∀ {Φ bs C A} →
  ForallsUsed (wrap-output bs C) →
  ForallsUsed (wrap-left-target bs A) →
  left-spine-ctx bs Φ ⊢ C ⊑ A →
  Φ ⊢ wrap-output bs C ⊑ wrap-left-target bs A
wrap-left-spine {bs = []} usedC usedA C⊑A = C⊑A
wrap-left-spine {Φ = Φ} {bs = both ∷ bs} {C = C} {A = A}
    usedC usedA C⊑A =
  ∀ⁱ_ {occA = ForallsUsed-∀-occ {A = wrap-output bs C} usedC}
      {occB = ForallsUsed-∀-occ {A = wrap-left-target bs A} usedA}
      (wrap-left-spine (ForallsUsed-∀-body {A = wrap-output bs C} usedC)
                       (ForallsUsed-∀-body
                         {A = wrap-left-target bs A} usedA)
                       C⊑A)
wrap-left-spine {Φ = Φ} {bs = leftOnly ∷ bs} {C = C} {A = A}
    usedC usedA C⊑A =
  ∀ⁱ_ {occA = ForallsUsed-∀-occ {A = wrap-output bs C} usedC}
      {occB = ForallsUsed-∀-occ {A = wrap-left-target bs A} usedA}
      (wrap-left-spine (ForallsUsed-∀-body {A = wrap-output bs C} usedC)
                       (ForallsUsed-∀-body
                         {A = wrap-left-target bs A} usedA)
                       C⊑A)
wrap-left-spine {Φ = Φ} {bs = rightOnly ∷ bs} {C = C} {A = A}
    usedC usedA C⊑A =
  ν (ForallsUsed-∀-occ {A = wrap-output bs C} usedC)
    (wrap-left-spine
      (ForallsUsed-∀-body {A = wrap-output bs C} usedC) usedA C⊑A)

wrap-right-spine :
  ∀ {Φ bs C B} →
  ForallsUsed (wrap-output bs C) →
  ForallsUsed (wrap-right-target bs B) →
  right-spine-ctx bs Φ ⊢ C ⊑ B →
  Φ ⊢ wrap-output bs C ⊑ wrap-right-target bs B
wrap-right-spine {bs = []} usedC usedB C⊑B = C⊑B
wrap-right-spine {Φ = Φ} {bs = both ∷ bs} {C = C} {B = B}
    usedC usedB C⊑B =
  ∀ⁱ_ {occA = ForallsUsed-∀-occ {A = wrap-output bs C} usedC}
      {occB = ForallsUsed-∀-occ {A = wrap-right-target bs B} usedB}
      (wrap-right-spine (ForallsUsed-∀-body {A = wrap-output bs C} usedC)
                        (ForallsUsed-∀-body
                          {A = wrap-right-target bs B} usedB)
                        C⊑B)
wrap-right-spine {Φ = Φ} {bs = leftOnly ∷ bs} {C = C} {B = B}
    usedC usedB C⊑B =
  ν (ForallsUsed-∀-occ {A = wrap-output bs C} usedC)
    (wrap-right-spine
      (ForallsUsed-∀-body {A = wrap-output bs C} usedC) usedB C⊑B)
wrap-right-spine {Φ = Φ} {bs = rightOnly ∷ bs} {C = C} {B = B}
    usedC usedB C⊑B =
  ∀ⁱ_ {occA = ForallsUsed-∀-occ {A = wrap-output bs C} usedC}
      {occB = ForallsUsed-∀-occ {A = wrap-right-target bs B} usedB}
      (wrap-right-spine (ForallsUsed-∀-body {A = wrap-output bs C} usedC)
                        (ForallsUsed-∀-body
                          {A = wrap-right-target bs B} usedB)
                        C⊑B)

left-spine-count-sound :
  ∀ {n m Γ₀ Γ A} →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  wrap-output (left-output-spine n m Γ₀ Γ) A ≡
  add∀ (mlb-∀-count n m Γ₀) A
left-spine-count-sound {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ} {A = A}
    noEsc≡ order≡ norm≡ =
  wrap-output-length {bs = left-output-spine n m Γ₀ Γ} {A = A}
    {k = mlb-∀-count n m Γ₀}
    (left-output-spine-length {n = n} {m = m} {Γ₀ = Γ₀} {Γ = Γ}
      noEsc≡ order≡ norm≡)

add∀-lower-left-spine :
  ∀ {Δ A n m A′ n∀A′ C₀ Γ₀ Γ C} →
  WfTy Δ A →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  split-∀ A ≡ (n , A′ , n∀A′) →
  add∀ (mlb-∀-count n m Γ₀)
    (renameᵗ (normalize-var n m Γ₀) C₀) ≡ C →
  ForallsUsed C →
  spine-left n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                        ⊑ left-normalized-target n m Γ₀ A′ →
  assm-left Γ ⊢ C ⊑ A
add∀-lower-left-spine {A = A} {n = n} {m = m} {A′ = A′}
    {C₀ = C₀} {Γ₀ = Γ₀} {Γ = Γ} {C = C}
    hA noEsc≡ order≡ norm≡ splitA≡ result≡ used C⊑A′ =
  subst (λ T → assm-left Γ ⊢ C ⊑ T) target≡
    (subst (λ S → assm-left Γ ⊢ S ⊑ target) source≡ wrapped)
  where
    body : Ty
    body = normalized-type n m Γ₀ C₀

    target : Ty
    target =
      wrap-left-target (left-output-spine n m Γ₀ Γ) A′

    source≡ : wrap-output (left-output-spine n m Γ₀ Γ) body ≡ C
    source≡ =
      trans (left-spine-count-sound {n = n} {m = m} {Γ₀ = Γ₀}
               {Γ = Γ} {A = body} noEsc≡ order≡ norm≡)
            result≡

    target≡ : target ≡ A
    target≡ =
      left-spine-target-sound {A = A} {n = n} {m = m} {A′ = A′}
        {Γ₀ = Γ₀} {Γ = Γ} noEsc≡ order≡ norm≡ splitA≡

    used′ : ForallsUsed (wrap-output (left-output-spine n m Γ₀ Γ) body)
    used′ = subst ForallsUsed (sym source≡) used

    target-used : ForallsUsed target
    target-used = subst ForallsUsed (sym target≡) (WfTy-foralls-used hA)

    body-lower :
      left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ)
        ⊢ body ⊑ A′
    body-lower =
      subst
        (λ T →
          left-spine-ctx (left-output-spine n m Γ₀ Γ) (assm-left Γ)
            ⊢ body ⊑ T)
        (left-normalized-target-cancel n m Γ₀ A′)
        (⊑-mono (left-spine-context-sound {n = n} {m = m}
                   {Γ₀ = Γ₀} {Γ = Γ} noEsc≡ order≡ norm≡)
                 C⊑A′)

    wrapped : assm-left Γ ⊢
      wrap-output (left-output-spine n m Γ₀ Γ) body ⊑ target
    wrapped = wrap-left-spine used′ target-used body-lower

postulate

  add∀-lower-right-spine :
    ∀ {Δ B n m B′ n∀B′ C₀ Γ₀ Γ C} →
    WfTy Δ B →
    no-escaping-assms? n m Γ₀ ≡ true →
    bound-var-var-order-ok-list? n m Γ₀ ≡ true →
    normalize-assms n m Γ₀ ≡ just Γ →
    split-∀ B ≡ (m , B′ , n∀B′) →
    add∀ (mlb-∀-count n m Γ₀)
      (renameᵗ (normalize-var n m Γ₀) C₀) ≡ C →
    ForallsUsed C →
    spine-right n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                           ⊑ right-normalized-target n m Γ₀ B′ →
    assm-right Γ ⊢ C ⊑ B

add∀-lower :
  ∀ {Δ A B n m A′ B′ n∀A′ n∀B′ C₀ Γ₀ Γ C} →
  WfTy Δ A →
  WfTy Δ B →
  no-escaping-assms? n m Γ₀ ≡ true →
  bound-var-var-order-ok-list? n m Γ₀ ≡ true →
  normalize-assms n m Γ₀ ≡ just Γ →
  split-∀ A ≡ (n , A′ , n∀A′) →
  split-∀ B ≡ (m , B′ , n∀B′) →
  add∀ (mlb-∀-count n m Γ₀)
    (renameᵗ (normalize-var n m Γ₀) C₀) ≡ C →
  ForallsUsed C →
  spine-left n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                        ⊑ left-normalized-target n m Γ₀ A′
    ×
  spine-right n m Γ₀ Γ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                         ⊑ right-normalized-target n m Γ₀ B′ →
  assm-left Γ ⊢ C ⊑ A × assm-right Γ ⊢ C ⊑ B
add∀-lower hA hB noEsc≡ order≡ norm≡ splitA≡ splitB≡ result≡ used
    (C⊑A′ , C⊑B′) =
  ( add∀-lower-left-spine hA noEsc≡ order≡ norm≡ splitA≡ result≡ used
      C⊑A′
  , add∀-lower-right-spine hB noEsc≡ order≡ norm≡ splitB≡ result≡ used
      C⊑B′
  )

residual-left-var-id :
  ∀ {Γ X Y} →
  residual-assms-ok? Γ ≡ true →
  (X ˣ⊑ˣ Y) ∈ assm-left Γ →
  X ≡ Y
residual-left-var-id {Γ = []} ok ()
residual-left-var-id {Γ = (x ~ᶜ y) ∷ Γ} ok x⊑y∈
    with x ≟ y
residual-left-var-id {Γ = (x ~ᶜ y) ∷ Γ} () x⊑y∈
    | no x≢y
residual-left-var-id {Γ = (x ~ᶜ .x) ∷ Γ} ok (here refl)
    | yes refl = refl
residual-left-var-id {Γ = (x ~ᶜ .x) ∷ Γ} ok (there x⊑y∈)
    | yes refl =
  residual-left-var-id ok x⊑y∈
residual-left-var-id {Γ = (x ~ᶜ★) ∷ Γ} () x⊑y∈
residual-left-var-id {Γ = (★~ᶜ x) ∷ Γ} () x⊑y∈

residual-right-var-id :
  ∀ {Γ X Y} →
  residual-assms-ok? Γ ≡ true →
  (X ˣ⊑ˣ Y) ∈ assm-right Γ →
  X ≡ Y
residual-right-var-id {Γ = []} ok ()
residual-right-var-id {Γ = (x ~ᶜ y) ∷ Γ} ok x⊑y∈
    with x ≟ y
residual-right-var-id {Γ = (x ~ᶜ y) ∷ Γ} () x⊑y∈
    | no x≢y
residual-right-var-id {Γ = (x ~ᶜ .x) ∷ Γ} ok (here refl)
    | yes refl = refl
residual-right-var-id {Γ = (x ~ᶜ .x) ∷ Γ} ok (there x⊑y∈)
    | yes refl =
  residual-right-var-id ok x⊑y∈
residual-right-var-id {Γ = (x ~ᶜ★) ∷ Γ} () x⊑y∈
residual-right-var-id {Γ = (★~ᶜ x) ∷ Γ} () x⊑y∈

residual-left-no-star :
  ∀ {Γ X} →
  residual-assms-ok? Γ ≡ true →
  (X ˣ⊑★) ∈ assm-left Γ →
  ⊥
residual-left-no-star {Γ = []} ok ()
residual-left-no-star {Γ = (x ~ᶜ y) ∷ Γ} ok x⊑★∈
    with x ≟ y
residual-left-no-star {Γ = (x ~ᶜ y) ∷ Γ} () x⊑★∈
    | no x≢y
residual-left-no-star {Γ = (x ~ᶜ .x) ∷ Γ} ok (there x⊑★∈)
    | yes refl =
  residual-left-no-star ok x⊑★∈
residual-left-no-star {Γ = (x ~ᶜ★) ∷ Γ} () x⊑★∈
residual-left-no-star {Γ = (★~ᶜ x) ∷ Γ} () x⊑★∈

residual-right-no-star :
  ∀ {Γ X} →
  residual-assms-ok? Γ ≡ true →
  (X ˣ⊑★) ∈ assm-right Γ →
  ⊥
residual-right-no-star {Γ = []} ok ()
residual-right-no-star {Γ = (x ~ᶜ y) ∷ Γ} ok x⊑★∈
    with x ≟ y
residual-right-no-star {Γ = (x ~ᶜ y) ∷ Γ} () x⊑★∈
    | no x≢y
residual-right-no-star {Γ = (x ~ᶜ .x) ∷ Γ} ok (there x⊑★∈)
    | yes refl =
  residual-right-no-star ok x⊑★∈
residual-right-no-star {Γ = (x ~ᶜ★) ∷ Γ} () x⊑★∈
residual-right-no-star {Γ = (★~ᶜ x) ∷ Γ} () x⊑★∈

record DischargeCtx (Δ : TyCtx) (Φ Ψ : ImpCtx) : Set where
  field
    discharge-var :
      ∀ {X Y} →
      Y < Δ →
      (X ˣ⊑ˣ Y) ∈ Φ →
      (X ˣ⊑ˣ Y) ∈ Ψ
    discharge-star :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Ψ

open DischargeCtx

discharge-∀ :
  ∀ {Δ Φ Ψ} →
  DischargeCtx Δ Φ Ψ →
  DischargeCtx (suc Δ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
discharge-∀ d .discharge-var {X = zero} {Y = zero} y<Δ
    (here refl) = here refl
discharge-∀ d .discharge-var {X = zero} {Y = zero} y<Δ
    (there x⊑y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y∈)
discharge-∀ d .discharge-var {X = zero} {Y = suc Y} y<Δ
    (there x⊑y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y∈)
discharge-∀ d .discharge-var {X = suc X} {Y = zero} y<Δ
    (there x⊑y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y∈)
discharge-∀ d .discharge-var {X = suc X} {Y = suc Y} (s<s y<Δ)
    (there x⊑y∈) =
  there (⇑ᵢ-ˣ∈ (discharge-var d y<Δ (un⇑ᵢ-ˣ∈ x⊑y∈)))
discharge-∀ d .discharge-star (here ())
discharge-∀ d .discharge-star {X = zero} (there x⊑★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★∈)
discharge-∀ d .discharge-star {X = suc X} (there x⊑★∈) =
  there (⇑ᵢ-★∈ (discharge-star d (un⇑ᵢ-★∈ x⊑★∈)))

discharge-ν :
  ∀ {Δ Φ Ψ} →
  DischargeCtx Δ Φ Ψ →
  DischargeCtx Δ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
discharge-ν d .discharge-var y<Δ (here ())
discharge-ν d .discharge-var {X = zero} y<Δ (there x⊑y∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y∈)
discharge-ν d .discharge-var {X = suc X} y<Δ (there x⊑y∈) =
  there (⇑ᴸᵢ-ˣ∈ (discharge-var d y<Δ (un⇑ᴸᵢ-ˣ∈ x⊑y∈)))
discharge-ν d .discharge-star (here refl) = here refl
discharge-ν d .discharge-star {X = zero} (there x⊑★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★∈)
discharge-ν d .discharge-star {X = suc X} (there x⊑★∈) =
  there (⇑ᴸᵢ-★∈ (discharge-star d (un⇑ᴸᵢ-★∈ x⊑★∈)))

⊑-discharge :
  ∀ {Δ Φ Ψ C A} →
  DischargeCtx Δ Φ Ψ →
  WfTy Δ A →
  Φ ⊢ C ⊑ A →
  Ψ ⊢ C ⊑ A
⊑-discharge d wf★ id★ = id★
⊑-discharge d (wfVar y<Δ) (idˣ x⊑y∈) =
  idˣ (discharge-var d y<Δ x⊑y∈)
⊑-discharge d wfBase idι = idι
⊑-discharge d (wf⇒ hA hB) (p ↦ q) =
  ⊑-discharge d hA p ↦ ⊑-discharge d hB q
⊑-discharge d (wf∀ {occ = occB} hB) (∀ⁱ_ {occA = occA} p) =
  ∀ⁱ_ {occA = occA} {occB = occB}
    (⊑-discharge (discharge-∀ d) hB p)
⊑-discharge d wf★ (tag ι) = tag ι
⊑-discharge d wf★ (tag_⇛_ p q) =
  tag_⇛_ (⊑-discharge d wf★ p) (⊑-discharge d wf★ q)
⊑-discharge d wf★ (tagˣ x⊑★∈) =
  tagˣ (discharge-star d x⊑★∈)
⊑-discharge d hB (ν occA p) =
  ν occA (⊑-discharge (discharge-ν d) hB p)

residual-left-discharge :
  ∀ {Δ Γ} →
  residual-assms-ok? Γ ≡ true →
  DischargeCtx Δ (assm-left Γ) (idᵢ Δ)
residual-left-discharge {Δ = Δ} ok .discharge-var {X = X} {Y = Y}
    y<Δ x⊑y∈ =
  subst (λ Z → (Z ˣ⊑ˣ Y) ∈ idᵢ Δ)
        (sym (residual-left-var-id ok x⊑y∈))
        (idᵢ-refl-∈ y<Δ)
residual-left-discharge ok .discharge-star x⊑★∈ =
  ⊥-elim (residual-left-no-star ok x⊑★∈)

residual-right-discharge :
  ∀ {Δ Γ} →
  residual-assms-ok? Γ ≡ true →
  DischargeCtx Δ (assm-right Γ) (idᵢ Δ)
residual-right-discharge {Δ = Δ} ok .discharge-var {X = X} {Y = Y}
    y<Δ x⊑y∈ =
  subst (λ Z → (Z ˣ⊑ˣ Y) ∈ idᵢ Δ)
        (sym (residual-right-var-id ok x⊑y∈))
        (idᵢ-refl-∈ y<Δ)
residual-right-discharge ok .discharge-star x⊑★∈ =
  ⊥-elim (residual-right-no-star ok x⊑★∈)

residual-assms-ok-lower :
  ∀ {Δ Γ C A B} →
  WfTy Δ A →
  WfTy Δ B →
  residual-assms-ok? Γ ≡ true →
  assm-left Γ ⊢ C ⊑ A × assm-right Γ ⊢ C ⊑ B →
  idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
residual-assms-ok-lower hA hB residual≡ (C⊑A , C⊑B) =
  ⊑-discharge (residual-left-discharge residual≡) hA C⊑A ,
  ⊑-discharge (residual-right-discharge residual≡) hB C⊑B

mutual
  {-# TERMINATING #-}
  core-mlb?-lower-raw :
    ∀ {Δ A B C Γ n∀A n∀B} →
    WfTy Δ A →
    WfTy Δ B →
    core-mlb? A B n∀A n∀B ≡ just (C , Γ) →
    assm-left Γ ⊢ C ⊑ A × assm-right Γ ⊢ C ⊑ B
  core-mlb?-lower-raw {A = `∀ A} {n∀A = ()}
  core-mlb?-lower-raw {B = `∀ B} {n∀B = ()}
  core-mlb?-lower-raw {A = ＇ X} {B = ＇ Y} hA hB refl =
    idˣ (here refl) , idˣ (here refl)
  core-mlb?-lower-raw {A = ＇ X} {B = ‵ ι} hA hB ()
  core-mlb?-lower-raw {A = ＇ X} {B = ★} hA hB refl =
    idˣ (here refl) , tagˣ (here refl)
  core-mlb?-lower-raw {A = ＇ X} {B = B₁ ⇒ B₂} hA hB ()
  core-mlb?-lower-raw {A = ‵ ι} {B = ＇ X} hA hB ()
  core-mlb?-lower-raw {A = ‵ ι₁} {B = ‵ ι₂} hA hB eq
      with ι₁ ≟Base ι₂
  core-mlb?-lower-raw {A = ‵ ι} {B = ‵ .ι} hA hB refl
      | yes refl = idι , idι
  core-mlb?-lower-raw {A = ‵ ι₁} {B = ‵ ι₂} hA hB ()
      | no neq
  core-mlb?-lower-raw {A = ‵ ι} {B = ★} hA hB refl =
    idι , tag ι
  core-mlb?-lower-raw {A = ‵ ι} {B = B₁ ⇒ B₂} hA hB ()
  core-mlb?-lower-raw {A = ★} {B = ＇ Y} hA hB refl =
    tagˣ (here refl) , idˣ (here refl)
  core-mlb?-lower-raw {A = ★} {B = ‵ ι} hA hB refl =
    tag ι , idι
  core-mlb?-lower-raw {A = ★} {B = ★} hA hB refl = id★ , id★
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) eq
      with search-mlb? ★ B₁ in s₁≡ | search-mlb? ★ B₂ in s₂≡
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) ()
      | nothing | s₂
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) ()
      | just r₁ | nothing
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) eq
      | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂ in merge≡
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) ()
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | nothing
  core-mlb?-lower-raw {A = ★} {B = B₁ ⇒ B₂} wf★ (wf⇒ hB₁ hB₂) refl
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | just Γ =
    ( tag_⇛_
        (⊑-mono left₁ (proj₁ lower₁))
        (⊑-mono left₂ (proj₁ lower₂))
    , ⊑-mono right₁ (proj₂ lower₁) ↦ ⊑-mono right₂ (proj₂ lower₂)
    )
    where
      lower₁ : assm-left Γ₁ ⊢ C₁ ⊑ ★ × assm-right Γ₁ ⊢ C₁ ⊑ B₁
      lower₁ = search-mlb?-lower-raw wf★ hB₁ s₁≡

      lower₂ : assm-left Γ₂ ⊢ C₂ ⊑ ★ × assm-right Γ₂ ⊢ C₂ ⊑ B₂
      lower₂ = search-mlb?-lower-raw wf★ hB₂ s₂≡

      left₁ : CtxIncl (assm-left Γ₁) (assm-left Γ)
      left₁ =
        assm-left-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      left₂ : CtxIncl (assm-left Γ₂) (assm-left Γ)
      left₂ =
        assm-left-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₁ : CtxIncl (assm-right Γ₁) (assm-right Γ)
      right₁ =
        assm-right-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₂ : CtxIncl (assm-right Γ₂) (assm-right Γ)
      right₂ =
        assm-right-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ＇ X} hA hB ()
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ‵ ι} hA hB ()
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ eq
      with search-mlb? A₁ ★ in s₁≡ | search-mlb? A₂ ★ in s₂≡
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ ()
      | nothing | s₂
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ ()
      | just r₁ | nothing
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ eq
      | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂ in merge≡
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ ()
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | nothing
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = ★} (wf⇒ hA₁ hA₂) wf★ refl
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | just Γ =
    ( ⊑-mono left₁ (proj₁ lower₁) ↦ ⊑-mono left₂ (proj₁ lower₂)
    , tag_⇛_
        (⊑-mono right₁ (proj₂ lower₁))
        (⊑-mono right₂ (proj₂ lower₂))
    )
    where
      lower₁ : assm-left Γ₁ ⊢ C₁ ⊑ A₁ × assm-right Γ₁ ⊢ C₁ ⊑ ★
      lower₁ = search-mlb?-lower-raw hA₁ wf★ s₁≡

      lower₂ : assm-left Γ₂ ⊢ C₂ ⊑ A₂ × assm-right Γ₂ ⊢ C₂ ⊑ ★
      lower₂ = search-mlb?-lower-raw hA₂ wf★ s₂≡

      left₁ : CtxIncl (assm-left Γ₁) (assm-left Γ)
      left₁ =
        assm-left-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      left₂ : CtxIncl (assm-left Γ₂) (assm-left Γ)
      left₂ =
        assm-left-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₁ : CtxIncl (assm-right Γ₁) (assm-right Γ)
      right₁ =
        assm-right-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₂ : CtxIncl (assm-right Γ₂) (assm-right Γ)
      right₂ =
        assm-right-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
      with search-mlb? A₁ B₁ in s₁≡ | search-mlb? A₂ B₂ in s₂≡
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) ()
      | nothing | s₂
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) ()
      | just r₁ | nothing
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
      | just (C₁ , Γ₁) | just (C₂ , Γ₂)
      with merge-assms Γ₁ Γ₂ in merge≡
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) ()
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | nothing
  core-mlb?-lower-raw {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) refl
      | just (C₁ , Γ₁) | just (C₂ , Γ₂) | just Γ =
    ( ⊑-mono left₁ (proj₁ lower₁) ↦ ⊑-mono left₂ (proj₁ lower₂)
    , ⊑-mono right₁ (proj₂ lower₁) ↦ ⊑-mono right₂ (proj₂ lower₂)
    )
    where
      lower₁ : assm-left Γ₁ ⊢ C₁ ⊑ A₁ × assm-right Γ₁ ⊢ C₁ ⊑ B₁
      lower₁ = search-mlb?-lower-raw hA₁ hB₁ s₁≡

      lower₂ : assm-left Γ₂ ⊢ C₂ ⊑ A₂ × assm-right Γ₂ ⊢ C₂ ⊑ B₂
      lower₂ = search-mlb?-lower-raw hA₂ hB₂ s₂≡

      left₁ : CtxIncl (assm-left Γ₁) (assm-left Γ)
      left₁ =
        assm-left-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      left₂ : CtxIncl (assm-left Γ₂) (assm-left Γ)
      left₂ =
        assm-left-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₁ : CtxIncl (assm-right Γ₁) (assm-right Γ)
      right₁ =
        assm-right-incl
          (merge-assms-left {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

      right₂ : CtxIncl (assm-right Γ₂) (assm-right Γ)
      right₂ =
        assm-right-incl
          (merge-assms-right {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ = Γ} merge≡)

  {-# TERMINATING #-}
  search-mlb?-lower-raw :
    ∀ {Δ A B C Γ} →
    WfTy Δ A →
    WfTy Δ B →
    search-mlb? A B ≡ just (C , Γ) →
    assm-left Γ ⊢ C ⊑ A × assm-right Γ ⊢ C ⊑ B
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      with split-∀ A in splitA≡ | split-∀ B in splitB≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′
      with core-mlb?
             (renameᵗ (embed-left-var n m) A′)
             (renameᵗ (embed-right-var n m) B′)
             (rename-non∀ n∀A′)
             (rename-non∀ n∀B′) in core≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB ()
      | n , A′ , n∀A′ | m , B′ , n∀B′ | nothing
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀)
      with no-escaping-assms? n m Γ₀ in noEsc≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB ()
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | false
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      with bound-var-var-order-ok-list? n m Γ₀ in order≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB ()
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | false
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true
      with normalize-assms n m Γ₀ in norm≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB ()
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true | nothing
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true | just Γ′
      with add∀ (mlb-∀-count n m Γ₀)
                 (renameᵗ (normalize-var n m Γ₀) C₀) in result≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB search≡
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true | just Γ′ | C′
      with foralls-used? C′ in used≡
  search-mlb?-lower-raw {A = A} {B = B} hA hB ()
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true | just Γ′ | C′ | false
  search-mlb?-lower-raw {Δ = Δ} {A = A} {B = B} hA hB refl
      | n , A′ , n∀A′ | m , B′ , n∀B′ | just (C₀ , Γ₀) | true
      | true | just Γ′ | C′ | true =
    wrapped-lower
    where
      splitA-wf : WfTy (n + Δ) A′
      splitA-wf = split-∀-wf hA splitA≡

      splitB-wf : WfTy (m + Δ) B′
      splitB-wf = split-∀-wf hB splitB≡

      embedded-left-wf :
        WfTy (n + m + Δ)
          (renameᵗ (embed-left-var n m) A′)
      embedded-left-wf =
        embed-left-wf {Δ = Δ} {n = n} {m = m} {A = A′} splitA-wf

      embedded-right-wf :
        WfTy (n + m + Δ)
          (renameᵗ (embed-right-var n m) B′)
      embedded-right-wf =
        embed-right-wf {Δ = Δ} {n = n} {m = m} {B = B′} splitB-wf

      raw-lower :
        assm-left Γ₀ ⊢ C₀ ⊑ renameᵗ (embed-left-var n m) A′
          ×
        assm-right Γ₀ ⊢ C₀ ⊑ renameᵗ (embed-right-var n m) B′
      raw-lower =
        core-mlb?-lower-raw embedded-left-wf embedded-right-wf core≡

      normalized-lower :
        spine-left n m Γ₀ Γ′ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                                ⊑ left-normalized-target n m Γ₀ A′
          ×
        spine-right n m Γ₀ Γ′ ⊢ renameᵗ (normalize-var n m Γ₀) C₀
                                 ⊑ right-normalized-target n m Γ₀ B′
      normalized-lower =
        normalize-lower-spine noEsc≡ order≡ norm≡ raw-lower

      used-sound : ForallsUsed C′
      used-sound = foralls-used?-sound {A = C′} used≡

      wrapped-lower :
        assm-left Γ′ ⊢ C′ ⊑ A × assm-right Γ′ ⊢ C′ ⊑ B
      wrapped-lower =
        add∀-lower hA hB noEsc≡ order≡ norm≡ splitA≡ splitB≡ result≡
          used-sound normalized-lower

search-mlb?-lower :
  ∀ {Δ A B C Γ} →
  WfTy Δ A →
  WfTy Δ B →
  search-mlb? A B ≡ just (C , Γ) →
  residual-assms-ok? Γ ≡ true →
  idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
search-mlb?-lower hA hB search≡ residual≡ =
  residual-assms-ok-lower hA hB residual≡
    (search-mlb?-lower-raw hA hB search≡)

mlb?-lower :
  ∀ {Δ A B C} →
  WfTy Δ A →
  WfTy Δ B →
  mlb? A B ≡ just C →
  idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
mlb?-lower {A = A} {B = B} hA hB eq
    with search-mlb? A B in search≡
mlb?-lower {A = A} {B = B} hA hB () | nothing
mlb?-lower {A = A} {B = B} hA hB eq | just (C′ , Γ)
    with residual-assms-ok? Γ in residual≡
mlb?-lower {A = A} {B = B} hA hB () | just (C′ , Γ) | false
mlb?-lower {A = A} {B = B} hA hB refl | just (C , Γ) | true =
  search-mlb?-lower hA hB search≡ residual≡

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
mlb-type {Γ = Γ} (p₁ ↦ p₂) (tag_⇛_ q₁ q₂) =
  mlb-type p₁ q₁ ⇒ mlb-type p₂ q₂
mlb-type {Γ = Γ} (∀ⁱ p) (∀ⁱ q) =
  `∀ (mlb-type {Γ = same ∷ Γ} p q)
mlb-type {Γ = Γ} (∀ⁱ p) (ν occ q) =
  `∀ (mlb-type {Γ = left ∷ Γ} p q)
mlb-type {Γ = Γ} (tag ι) idι = ‵ ι
mlb-type {Γ = Γ} (tag ι) (tag .ι) = ★
mlb-type {Γ = Γ} (tag_⇛_ p₁ p₂) (q₁ ↦ q₂) =
  mlb-type p₁ q₁ ⇒ mlb-type p₂ q₂
mlb-type {Γ = Γ} (tag_⇛_ p₁ p₂) (tag_⇛_ q₁ q₂) = ★
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
    ; lower-left = tag_⇛_ (lower-left mlb₁) (lower-left mlb₂)
    ; lower-right = lower-right mlb₁ ↦ lower-right mlb₂
    ; maximal = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBound _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelow _ (lower mlb₁ ⇒ lower mlb₂) D
    maximal′ ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximal mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximal mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇛_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximal :
  ∀ {Δ A₁ A₂} →
  MaximalLowerBound Δ A₁ ★ →
  MaximalLowerBound Δ A₂ ★ →
  MaximalLowerBound Δ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximal mlb₁ mlb₂ =
  record
    { lower = lower mlb₁ ⇒ lower mlb₂
    ; lower-left = lower-left mlb₁ ↦ lower-left mlb₂
    ; lower-right = tag_⇛_ (lower-right mlb₁) (lower-right mlb₂)
    ; maximal = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBound _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelow _ (lower mlb₁ ⇒ lower mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
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
    ; lower-leftᶜ = tag_⇛_ (lower-leftᶜ mlb₁) (lower-leftᶜ mlb₂)
    ; lower-rightᶜ = lower-rightᶜ mlb₁ ↦ lower-rightᶜ mlb₂
    ; maximalᶜ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelowᶜ _ (lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂) D
    maximal′ ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜ mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜ mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇛_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximalᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ A₂} →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₁ ★ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ A₂ ★ →
  MaximalLowerBoundᶜ Φᴸ Φᴿ Φᴼ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximalᶜ mlb₁ mlb₂ =
  record
    { lowerᶜ = lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂
    ; lower-leftᶜ = lower-leftᶜ mlb₁ ↦ lower-leftᶜ mlb₂
    ; lower-rightᶜ = tag_⇛_ (lower-rightᶜ mlb₁) (lower-rightᶜ mlb₂)
    ; maximalᶜ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜ _ _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelowᶜ _ (lowerᶜ mlb₁ ⇒ lowerᶜ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
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
    liftCtx νᵇ Φᴿ ⊢ C ⊑ `∀ B →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

  ff-via-ν∀ :
    ∀ {A B C}
      {occC : occurs zero C ≡ true}
      {occB : occurs zero B ≡ true} →
    liftCtx νᵇ Φᴸ ⊢ C ⊑ `∀ A →
    liftCtx ∀ᵇ Φᴿ ⊢ C ⊑ B →
    ForallForallLower²ᶜ Φᴸ Φᴿ (`∀ C) A B

  ff-via-νν :
    ∀ {A B C} →
    occurs zero C ≡ true →
    liftCtx νᵇ Φᴸ ⊢ C ⊑ `∀ A →
    liftCtx νᵇ Φᴿ ⊢ C ⊑ `∀ B →
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
      liftCtx νᵇ Φᴿ ⊢ D ⊑ `∀ B →
      Φᴼ ⊢ `∀ D ⊑ `∀ C

    kν∀ :
      ∀ {D} →
      occurs zero D ≡ true →
      liftCtx νᵇ Φᴸ ⊢ D ⊑ `∀ A →
      liftCtx ∀ᵇ Φᴿ ⊢ D ⊑ B →
      occurs zero B ≡ true →
      Φᴼ ⊢ `∀ D ⊑ `∀ C

    kνν :
      ∀ {D} →
      occurs zero D ≡ true →
      liftCtx νᵇ Φᴸ ⊢ D ⊑ `∀ A →
      liftCtx νᵇ Φᴿ ⊢ D ⊑ `∀ B →
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
