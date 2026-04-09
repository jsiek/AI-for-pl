module extrinsic.TypeTermSubst where

-- File Charter:
--   * Type-level action on terms (`renameᵀ` / `substᵀ`) support lemmas.
--   * This module is part of the ongoing refactor that moved substitution
--     metatheory out of `Terms.agda`.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z<s; s<s)
open import extrinsic.Terms
open import extrinsic.TypeSubst as TS

cong₃ : ∀ {A B C D : Set}
  (f : A → B → C → D)
  {x x' : A} {y y' : B} {z z' : C}
  → x ≡ x'
  → y ≡ y'
  → z ≡ z'
  → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

cong-ƛ : ∀ {A : Ty} {M N : Term}
  → M ≡ N
  → (ƛ[ A ] M) ≡ (ƛ[ A ] N)
cong-ƛ {A = A} = cong (ƛ[ A ]_)

cong-·[] : ∀ {A : Ty} {M N : Term}
  → M ≡ N
  → (M ·[ A ]) ≡ (N ·[ A ])
cong-·[] {A = A} = cong (λ X → X ·[ A ])

------------------------------------------------------------------------
-- Type renaming/substitution congruence
------------------------------------------------------------------------

extᵗ-cong : ∀ {ρ ρ' : Renameᵗ}
  → ((i : Var) → ρ i ≡ ρ' i)
  → (i : Var) → extᵗ ρ i ≡ extᵗ ρ' i
extᵗ-cong h 0 = refl
extᵗ-cong h (suc i) = cong suc (h i)

renameᵀ-cong : ∀ {ρ ρ' : Renameᵗ}
  → ((i : Var) → ρ i ≡ ρ' i)
  → (M : Term)
  → renameᵀ ρ M ≡ renameᵀ ρ' M
renameᵀ-cong h (` i) = refl
renameᵀ-cong h (ƛ[ A ] N) = cong₂ ƛ[_]_ (TS.rename-cong h A) (renameᵀ-cong h N)
renameᵀ-cong h (L · M) = cong₂ _·_ (renameᵀ-cong h L) (renameᵀ-cong h M)
renameᵀ-cong h `true = refl
renameᵀ-cong h `false = refl
renameᵀ-cong h `zero = refl
renameᵀ-cong h (`suc M) = cong `suc_ (renameᵀ-cong h M)
renameᵀ-cong h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (renameᵀ-cong h L) (renameᵀ-cong h M) (renameᵀ-cong h N)
renameᵀ-cong h (`if_then_else L M N) =
  cong₃ `if_then_else (renameᵀ-cong h L) (renameᵀ-cong h M) (renameᵀ-cong h N)
renameᵀ-cong h (Λ N) = cong Λ_ (renameᵀ-cong (extᵗ-cong h) N)
renameᵀ-cong h (M ·[ A ]) =
  cong₂ _·[_] (renameᵀ-cong h M) (TS.rename-cong h A)

extsᵗ-cong : ∀ {σ τ : Substᵗ}
  → ((i : Var) → σ i ≡ τ i)
  → (i : Var) → extsᵗ σ i ≡ extsᵗ τ i
extsᵗ-cong h 0 = refl
extsᵗ-cong h (suc i) = cong (renameᵗ suc) (h i)

substᵀ-cong : ∀ {σ τ : Substᵗ}
  → ((i : Var) → σ i ≡ τ i)
  → (M : Term)
  → substᵀ σ M ≡ substᵀ τ M
substᵀ-cong h (` i) = refl
substᵀ-cong h (ƛ[ A ] N) = cong₂ ƛ[_]_ (TS.subst-cong h A) (substᵀ-cong h N)
substᵀ-cong h (L · M) = cong₂ _·_ (substᵀ-cong h L) (substᵀ-cong h M)
substᵀ-cong h `true = refl
substᵀ-cong h `false = refl
substᵀ-cong h `zero = refl
substᵀ-cong h (`suc M) = cong `suc_ (substᵀ-cong h M)
substᵀ-cong h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (substᵀ-cong h L) (substᵀ-cong h M) (substᵀ-cong h N)
substᵀ-cong h (`if_then_else L M N) =
  cong₃ `if_then_else (substᵀ-cong h L) (substᵀ-cong h M) (substᵀ-cong h N)
substᵀ-cong h (Λ N) = cong Λ_ (substᵀ-cong (extsᵗ-cong h) N)
substᵀ-cong h (M ·[ A ]) =
  cong₂ _·[_] (substᵀ-cong h M) (TS.subst-cong h A)

------------------------------------------------------------------------
-- Type renamings/substitutions commute
------------------------------------------------------------------------

renameᵀ-renameᵀ : (ρ₁ ρ₂ : Renameᵗ) (M : Term)
  → renameᵀ ρ₂ (renameᵀ ρ₁ M) ≡ renameᵀ (λ i → ρ₂ (ρ₁ i)) M
renameᵀ-renameᵀ ρ₁ ρ₂ (` i) = refl
renameᵀ-renameᵀ ρ₁ ρ₂ (ƛ[ A ] N) =
  cong₂ ƛ[_]_ (TS.rename-rename-commute ρ₁ ρ₂ A) (renameᵀ-renameᵀ ρ₁ ρ₂ N)
renameᵀ-renameᵀ ρ₁ ρ₂ (L · M) =
  cong₂ _·_ (renameᵀ-renameᵀ ρ₁ ρ₂ L) (renameᵀ-renameᵀ ρ₁ ρ₂ M)
renameᵀ-renameᵀ ρ₁ ρ₂ `true = refl
renameᵀ-renameᵀ ρ₁ ρ₂ `false = refl
renameᵀ-renameᵀ ρ₁ ρ₂ `zero = refl
renameᵀ-renameᵀ ρ₁ ρ₂ (`suc M) = cong `suc_ (renameᵀ-renameᵀ ρ₁ ρ₂ M)
renameᵀ-renameᵀ ρ₁ ρ₂ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (renameᵀ-renameᵀ ρ₁ ρ₂ L)
    (renameᵀ-renameᵀ ρ₁ ρ₂ M)
    (renameᵀ-renameᵀ ρ₁ ρ₂ N)
renameᵀ-renameᵀ ρ₁ ρ₂ (`if_then_else L M N) =
  cong₃ `if_then_else
    (renameᵀ-renameᵀ ρ₁ ρ₂ L)
    (renameᵀ-renameᵀ ρ₁ ρ₂ M)
    (renameᵀ-renameᵀ ρ₁ ρ₂ N)
renameᵀ-renameᵀ ρ₁ ρ₂ (Λ N) =
  cong Λ_
    (trans
      (renameᵀ-renameᵀ (extᵗ ρ₁) (extᵗ ρ₂) N)
      (renameᵀ-cong (TS.ext-comp ρ₁ ρ₂) N))
renameᵀ-renameᵀ ρ₁ ρ₂ (M ·[ A ]) =
  cong₂ _·[_] (renameᵀ-renameᵀ ρ₁ ρ₂ M) (TS.rename-rename-commute ρ₁ ρ₂ A)

renameᵀ-suc-extᵗ : (ρᵗ : Renameᵗ) (M : Term)
  → renameᵀ suc (renameᵀ ρᵗ M) ≡ renameᵀ (extᵗ ρᵗ) (renameᵀ suc M)
renameᵀ-suc-extᵗ ρᵗ M =
  trans
    (renameᵀ-renameᵀ ρᵗ suc M)
    (trans
      (renameᵀ-cong (λ i → refl) M)
      (sym (renameᵀ-renameᵀ suc (extᵗ ρᵗ) M)))

substᵀ-renameᵀ-commute : (ρᵗ : Renameᵗ) (τ : Substᵗ) (M : Term)
  → substᵀ τ (renameᵀ ρᵗ M) ≡ substᵀ (λ i → τ (ρᵗ i)) M
substᵀ-renameᵀ-commute ρᵗ τ (` i) = refl
substᵀ-renameᵀ-commute ρᵗ τ (ƛ[ A ] N) =
  cong₂ ƛ[_]_
    (TS.rename-subst-commute ρᵗ τ A)
    (substᵀ-renameᵀ-commute ρᵗ τ N)
substᵀ-renameᵀ-commute ρᵗ τ (L · M) =
  cong₂ _·_
    (substᵀ-renameᵀ-commute ρᵗ τ L)
    (substᵀ-renameᵀ-commute ρᵗ τ M)
substᵀ-renameᵀ-commute ρᵗ τ `true = refl
substᵀ-renameᵀ-commute ρᵗ τ `false = refl
substᵀ-renameᵀ-commute ρᵗ τ `zero = refl
substᵀ-renameᵀ-commute ρᵗ τ (`suc M) =
  cong `suc_ (substᵀ-renameᵀ-commute ρᵗ τ M)
substᵀ-renameᵀ-commute ρᵗ τ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (substᵀ-renameᵀ-commute ρᵗ τ L)
    (substᵀ-renameᵀ-commute ρᵗ τ M)
    (substᵀ-renameᵀ-commute ρᵗ τ N)
substᵀ-renameᵀ-commute ρᵗ τ (`if_then_else L M N) =
  cong₃ `if_then_else
    (substᵀ-renameᵀ-commute ρᵗ τ L)
    (substᵀ-renameᵀ-commute ρᵗ τ M)
    (substᵀ-renameᵀ-commute ρᵗ τ N)
substᵀ-renameᵀ-commute ρᵗ τ (Λ N) =
  cong Λ_
    (trans
      (substᵀ-renameᵀ-commute (extᵗ ρᵗ) (extsᵗ τ) N)
      (substᵀ-cong (TS.exts-ext-comp ρᵗ τ) N))
substᵀ-renameᵀ-commute ρᵗ τ (M ·[ A ]) =
  cong₂ _·[_]
    (substᵀ-renameᵀ-commute ρᵗ τ M)
    (TS.rename-subst-commute ρᵗ τ A)

renameᵀ-substᵀ : (ρᵗ : Renameᵗ) (τ : Substᵗ) (M : Term)
  → renameᵀ ρᵗ (substᵀ τ M) ≡ substᵀ (λ i → renameᵗ ρᵗ (τ i)) M
renameᵀ-substᵀ ρᵗ τ (` i) = refl
renameᵀ-substᵀ ρᵗ τ (ƛ[ A ] N) =
  cong₂ ƛ[_]_
    (TS.rename-subst ρᵗ τ A)
    (renameᵀ-substᵀ ρᵗ τ N)
renameᵀ-substᵀ ρᵗ τ (L · M) =
  cong₂ _·_
    (renameᵀ-substᵀ ρᵗ τ L)
    (renameᵀ-substᵀ ρᵗ τ M)
renameᵀ-substᵀ ρᵗ τ `true = refl
renameᵀ-substᵀ ρᵗ τ `false = refl
renameᵀ-substᵀ ρᵗ τ `zero = refl
renameᵀ-substᵀ ρᵗ τ (`suc M) =
  cong `suc_ (renameᵀ-substᵀ ρᵗ τ M)
renameᵀ-substᵀ ρᵗ τ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (renameᵀ-substᵀ ρᵗ τ L)
    (renameᵀ-substᵀ ρᵗ τ M)
    (renameᵀ-substᵀ ρᵗ τ N)
renameᵀ-substᵀ ρᵗ τ (`if_then_else L M N) =
  cong₃ `if_then_else
    (renameᵀ-substᵀ ρᵗ τ L)
    (renameᵀ-substᵀ ρᵗ τ M)
    (renameᵀ-substᵀ ρᵗ τ N)
renameᵀ-substᵀ ρᵗ τ (Λ N) =
  cong Λ_
    (trans
      (renameᵀ-substᵀ (extᵗ ρᵗ) (extsᵗ τ) N)
      (substᵀ-cong (TS.ext-exts-comp ρᵗ τ) N))
renameᵀ-substᵀ ρᵗ τ (M ·[ A ]) =
  cong₂ _·[_]
    (renameᵀ-substᵀ ρᵗ τ M)
    (TS.rename-subst ρᵗ τ A)

renameᵀ-suc-extsᵗ : (τ : Substᵗ) (M : Term)
  → renameᵀ suc (substᵀ τ M) ≡ substᵀ (extsᵗ τ) (renameᵀ suc M)
renameᵀ-suc-extsᵗ τ M =
  trans
    (renameᵀ-substᵀ suc τ M)
    (trans
      (substᵀ-cong (λ i → refl) M)
      (sym (substᵀ-renameᵀ-commute suc (extsᵗ τ) M)))

substᵀ-substᵀ : (τ σ : Substᵗ) (M : Term)
  → substᵀ τ (substᵀ σ M) ≡ substᵀ (λ i → substᵗ τ (σ i)) M
substᵀ-substᵀ τ σ (` i) = refl
substᵀ-substᵀ τ σ (ƛ[ A ] N) =
  cong₂ ƛ[_]_
    (TS.sub-sub σ τ A)
    (substᵀ-substᵀ τ σ N)
substᵀ-substᵀ τ σ (L · M) =
  cong₂ _·_
    (substᵀ-substᵀ τ σ L)
    (substᵀ-substᵀ τ σ M)
substᵀ-substᵀ τ σ `true = refl
substᵀ-substᵀ τ σ `false = refl
substᵀ-substᵀ τ σ `zero = refl
substᵀ-substᵀ τ σ (`suc M) =
  cong `suc_ (substᵀ-substᵀ τ σ M)
substᵀ-substᵀ τ σ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (substᵀ-substᵀ τ σ L)
    (substᵀ-substᵀ τ σ M)
    (substᵀ-substᵀ τ σ N)
substᵀ-substᵀ τ σ (`if_then_else L M N) =
  cong₃ `if_then_else
    (substᵀ-substᵀ τ σ L)
    (substᵀ-substᵀ τ σ M)
    (substᵀ-substᵀ τ σ N)
substᵀ-substᵀ τ σ (Λ N) =
  cong Λ_
    (trans
      (substᵀ-substᵀ (extsᵗ τ) (extsᵗ σ) N)
      (substᵀ-cong exts-comp N))
  where
  exts-comp : (i : Var)
    → substᵗ (extsᵗ τ) (extsᵗ σ i) ≡ extsᵗ (λ j → substᵗ τ (σ j)) i
  exts-comp 0 = refl
  exts-comp (suc i) = TS.exts-seq σ τ (suc i)
substᵀ-substᵀ τ σ (M ·[ A ]) =
  cong₂ _·[_]
    (substᵀ-substᵀ τ σ M)
    (TS.sub-sub σ τ A)

------------------------------------------------------------------------
-- Mixed term and type renamings/substitutions commute
------------------------------------------------------------------------

rename-renameᵀ-commute : (ρ : Rename) (ρᵗ : Renameᵗ) (M : Term)
  → rename ρ (renameᵀ ρᵗ M) ≡ renameᵀ ρᵗ (rename ρ M)
rename-renameᵀ-commute ρ ρᵗ (` i) = refl
rename-renameᵀ-commute ρ ρᵗ (ƛ[ A ] N) =
  cong₂ ƛ[_]_ refl (rename-renameᵀ-commute (ext ρ) ρᵗ N)
rename-renameᵀ-commute ρ ρᵗ (L · M) =
  cong₂ _·_ (rename-renameᵀ-commute ρ ρᵗ L) (rename-renameᵀ-commute ρ ρᵗ M)
rename-renameᵀ-commute ρ ρᵗ `true = refl
rename-renameᵀ-commute ρ ρᵗ `false = refl
rename-renameᵀ-commute ρ ρᵗ `zero = refl
rename-renameᵀ-commute ρ ρᵗ (`suc M) =
  cong `suc_ (rename-renameᵀ-commute ρ ρᵗ M)
rename-renameᵀ-commute ρ ρᵗ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (rename-renameᵀ-commute ρ ρᵗ L)
    (rename-renameᵀ-commute ρ ρᵗ M)
    (rename-renameᵀ-commute (ext ρ) ρᵗ N)
rename-renameᵀ-commute ρ ρᵗ (`if_then_else L M N) =
  cong₃ `if_then_else
    (rename-renameᵀ-commute ρ ρᵗ L)
    (rename-renameᵀ-commute ρ ρᵗ M)
    (rename-renameᵀ-commute ρ ρᵗ N)
rename-renameᵀ-commute ρ ρᵗ (Λ N) =
  cong Λ_ (rename-renameᵀ-commute ρ (extᵗ ρᵗ) N)
rename-renameᵀ-commute ρ ρᵗ (M ·[ A ]) =
  cong₂ _·[_] (rename-renameᵀ-commute ρ ρᵗ M) refl

subst-renameᵀ-commute-gen : (σ τ : Subst) (ρᵗ : Renameᵗ)
  → ((i : Var) → τ i ≡ renameᵀ ρᵗ (σ i))
  → (M : Term)
  → subst τ (renameᵀ ρᵗ M) ≡ renameᵀ ρᵗ (subst σ M)
subst-renameᵀ-commute-gen σ τ ρᵗ h (` i) = h i
subst-renameᵀ-commute-gen σ τ ρᵗ h (ƛ[ A ] N) =
  cong₂ ƛ[_]_ refl
    (subst-renameᵀ-commute-gen (exts σ) (exts τ) ρᵗ (exts-comm h) N)
  where
  exts-comm : ((i : Var) → τ i ≡ renameᵀ ρᵗ (σ i))
    → (i : Var) → exts τ i ≡ renameᵀ ρᵗ (exts σ i)
  exts-comm h 0 = refl
  exts-comm h (suc i) =
    trans
      (cong (rename suc) (h i))
      (rename-renameᵀ-commute suc ρᵗ (σ i))
subst-renameᵀ-commute-gen σ τ ρᵗ h (L · M) =
  cong₂ _·_
    (subst-renameᵀ-commute-gen σ τ ρᵗ h L)
    (subst-renameᵀ-commute-gen σ τ ρᵗ h M)
subst-renameᵀ-commute-gen σ τ ρᵗ h `true = refl
subst-renameᵀ-commute-gen σ τ ρᵗ h `false = refl
subst-renameᵀ-commute-gen σ τ ρᵗ h `zero = refl
subst-renameᵀ-commute-gen σ τ ρᵗ h (`suc M) =
  cong `suc_ (subst-renameᵀ-commute-gen σ τ ρᵗ h M)
subst-renameᵀ-commute-gen σ τ ρᵗ h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (subst-renameᵀ-commute-gen σ τ ρᵗ h L)
    (subst-renameᵀ-commute-gen σ τ ρᵗ h M)
    (subst-renameᵀ-commute-gen (exts σ) (exts τ) ρᵗ (exts-comm h) N)
  where
  exts-comm : ((i : Var) → τ i ≡ renameᵀ ρᵗ (σ i))
    → (i : Var) → exts τ i ≡ renameᵀ ρᵗ (exts σ i)
  exts-comm h 0 = refl
  exts-comm h (suc i) =
    trans
      (cong (rename suc) (h i))
      (rename-renameᵀ-commute suc ρᵗ (σ i))
subst-renameᵀ-commute-gen σ τ ρᵗ h (`if_then_else L M N) =
  cong₃ `if_then_else
    (subst-renameᵀ-commute-gen σ τ ρᵗ h L)
    (subst-renameᵀ-commute-gen σ τ ρᵗ h M)
    (subst-renameᵀ-commute-gen σ τ ρᵗ h N)
subst-renameᵀ-commute-gen σ τ ρᵗ h (Λ N) =
  cong Λ_
    (subst-renameᵀ-commute-gen (⇑ σ) (⇑ τ) (extᵗ ρᵗ) (⇑-comm h) N)
  where
  ⇑-comm : ((i : Var) → τ i ≡ renameᵀ ρᵗ (σ i))
    → (i : Var) → ⇑ τ i ≡ renameᵀ (extᵗ ρᵗ) (⇑ σ i)
  ⇑-comm h i =
    trans
      (cong (renameᵀ suc) (h i))
      (renameᵀ-suc-extᵗ ρᵗ (σ i))
subst-renameᵀ-commute-gen σ τ ρᵗ h (M ·[ A ]) =
  cong₂ _·[_] (subst-renameᵀ-commute-gen σ τ ρᵗ h M) refl

subst-renameᵀ-commute : (σ : Subst) (ρᵗ : Renameᵗ) (M : Term)
  → subst (λ i → renameᵀ ρᵗ (σ i)) (renameᵀ ρᵗ M) ≡ renameᵀ ρᵗ (subst σ M)
subst-renameᵀ-commute σ ρᵗ M =
  subst-renameᵀ-commute-gen σ (λ i → renameᵀ ρᵗ (σ i)) ρᵗ (λ i → refl) M

rename-substᵀ-commute : (ρ : Rename) (τ : Substᵗ) (M : Term)
  → rename ρ (substᵀ τ M) ≡ substᵀ τ (rename ρ M)
rename-substᵀ-commute ρ τ (` i) = refl
rename-substᵀ-commute ρ τ (ƛ[ A ] N) =
  cong₂ ƛ[_]_ refl (rename-substᵀ-commute (ext ρ) τ N)
rename-substᵀ-commute ρ τ (L · M) =
  cong₂ _·_ (rename-substᵀ-commute ρ τ L) (rename-substᵀ-commute ρ τ M)
rename-substᵀ-commute ρ τ `true = refl
rename-substᵀ-commute ρ τ `false = refl
rename-substᵀ-commute ρ τ `zero = refl
rename-substᵀ-commute ρ τ (`suc M) =
  cong `suc_ (rename-substᵀ-commute ρ τ M)
rename-substᵀ-commute ρ τ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (rename-substᵀ-commute ρ τ L)
    (rename-substᵀ-commute ρ τ M)
    (rename-substᵀ-commute (ext ρ) τ N)
rename-substᵀ-commute ρ τ (`if_then_else L M N) =
  cong₃ `if_then_else
    (rename-substᵀ-commute ρ τ L)
    (rename-substᵀ-commute ρ τ M)
    (rename-substᵀ-commute ρ τ N)
rename-substᵀ-commute ρ τ (Λ N) =
  cong Λ_ (rename-substᵀ-commute ρ (extsᵗ τ) N)
rename-substᵀ-commute ρ τ (M ·[ A ]) =
  cong₂ _·[_] (rename-substᵀ-commute ρ τ M) refl

substᵀ-subst-commute-gen : (τ : Substᵗ) (σ σ' : Subst)
  → ((i : Var) → σ' i ≡ substᵀ τ (σ i))
  → (M : Term)
  → substᵀ τ (subst σ M) ≡ subst σ' (substᵀ τ M)
substᵀ-subst-commute-gen τ σ σ' h (` i) = sym (h i)
substᵀ-subst-commute-gen τ σ σ' h (ƛ[ A ] N) =
  cong₂ ƛ[_]_ refl
    (substᵀ-subst-commute-gen τ (exts σ) (exts σ') (exts-comm h) N)
  where
  exts-comm : ((i : Var) → σ' i ≡ substᵀ τ (σ i))
    → (i : Var) → exts σ' i ≡ substᵀ τ (exts σ i)
  exts-comm h 0 = refl
  exts-comm h (suc i) =
    trans
      (cong (rename suc) (h i))
      (rename-substᵀ-commute suc τ (σ i))
substᵀ-subst-commute-gen τ σ σ' h (L · M) =
  cong₂ _·_
    (substᵀ-subst-commute-gen τ σ σ' h L)
    (substᵀ-subst-commute-gen τ σ σ' h M)
substᵀ-subst-commute-gen τ σ σ' h `true = refl
substᵀ-subst-commute-gen τ σ σ' h `false = refl
substᵀ-subst-commute-gen τ σ σ' h `zero = refl
substᵀ-subst-commute-gen τ σ σ' h (`suc M) =
  cong `suc_ (substᵀ-subst-commute-gen τ σ σ' h M)
substᵀ-subst-commute-gen τ σ σ' h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_]
    (substᵀ-subst-commute-gen τ σ σ' h L)
    (substᵀ-subst-commute-gen τ σ σ' h M)
    (substᵀ-subst-commute-gen τ (exts σ) (exts σ') (exts-comm h) N)
  where
  exts-comm : ((i : Var) → σ' i ≡ substᵀ τ (σ i))
    → (i : Var) → exts σ' i ≡ substᵀ τ (exts σ i)
  exts-comm h 0 = refl
  exts-comm h (suc i) =
    trans
      (cong (rename suc) (h i))
      (rename-substᵀ-commute suc τ (σ i))
substᵀ-subst-commute-gen τ σ σ' h (`if_then_else L M N) =
  cong₃ `if_then_else
    (substᵀ-subst-commute-gen τ σ σ' h L)
    (substᵀ-subst-commute-gen τ σ σ' h M)
    (substᵀ-subst-commute-gen τ σ σ' h N)
substᵀ-subst-commute-gen τ σ σ' h (Λ N) =
  cong Λ_
    (substᵀ-subst-commute-gen (extsᵗ τ) (⇑ σ) (⇑ σ') (⇑-comm h) N)
  where
  ⇑-comm : ((i : Var) → σ' i ≡ substᵀ τ (σ i))
    → (i : Var) → ⇑ σ' i ≡ substᵀ (extsᵗ τ) (⇑ σ i)
  ⇑-comm h i =
    trans
      (cong (renameᵀ suc) (h i))
      (renameᵀ-suc-extsᵗ τ (σ i))
substᵀ-subst-commute-gen τ σ σ' h (M ·[ A ]) =
  cong₂ _·[_] (substᵀ-subst-commute-gen τ σ σ' h M) refl

substᵀ-subst-commute : (τ : Substᵗ) (σ : Subst) (M : Term)
  → substᵀ τ (subst σ M) ≡ subst (λ i → substᵀ τ (σ i)) (substᵀ τ M)
substᵀ-subst-commute τ σ M =
  substᵀ-subst-commute-gen τ σ (λ i → substᵀ τ (σ i)) (λ i → refl) M

------------------------------------------------------------------------
-- Substitution identity
------------------------------------------------------------------------

extsᵗ-id : (i : Var) → extsᵗ idᵗ i ≡ idᵗ i
extsᵗ-id 0 = refl
extsᵗ-id (suc i) = refl

substᵀ-id : (M : Term) → substᵀ idᵗ M ≡ M
substᵀ-id (` i) = refl
substᵀ-id (ƛ[ A ] N) =
  cong₂ ƛ[_]_
    (TS.subst-id A)
    (substᵀ-id N)
substᵀ-id (L · M) = cong₂ _·_ (substᵀ-id L) (substᵀ-id M)
substᵀ-id `true = refl
substᵀ-id `false = refl
substᵀ-id `zero = refl
substᵀ-id (`suc M) = cong `suc_ (substᵀ-id M)
substᵀ-id (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (substᵀ-id L) (substᵀ-id M) (substᵀ-id N)
substᵀ-id (`if_then_else L M N) =
  cong₃ `if_then_else (substᵀ-id L) (substᵀ-id M) (substᵀ-id N)
substᵀ-id (Λ N) =
  cong Λ_
    (trans
      (substᵀ-cong extsᵗ-id N)
      (substᵀ-id N))
substᵀ-id (M ·[ A ]) =
  cong₂ _·[_] (substᵀ-id M) (TS.subst-id A)

------------------------------------------------------------------------
-- Substitution identity from typing (closed wrt type variables)
------------------------------------------------------------------------

IdOnΔ : TyCtx → Substᵗ → Set
IdOnΔ Δ σ = ∀ {X} → X < Δ → σ X ≡ ` X

IdOnΔ-exts :
  {Δ : TyCtx} {σ : Substᵗ} →
  IdOnΔ Δ σ →
  IdOnΔ (suc Δ) (extsᵗ σ)
IdOnΔ-exts hσ {zero} z<s = refl
IdOnΔ-exts hσ {suc X} (s<s x<Δ) =
  cong (renameᵗ suc) (hσ x<Δ)

substᵗ-id-typed :
  {Δ : TyCtx} {A : Ty} {σ : Substᵗ} →
  IdOnΔ Δ σ →
  WfTy Δ A →
  substᵗ σ A ≡ A
substᵗ-id-typed hσ (wfVar x<Δ) = hσ x<Δ
substᵗ-id-typed hσ wf`ℕ = refl
substᵗ-id-typed hσ wf`Bool = refl
substᵗ-id-typed hσ (wfFn hA hB) =
  cong₂ _⇒_
    (substᵗ-id-typed hσ hA)
    (substᵗ-id-typed hσ hB)
substᵗ-id-typed hσ (wf`∀ hA) =
  cong `∀ (substᵗ-id-typed (IdOnΔ-exts hσ) hA)

substᵀ-id-typed :
  {Δ : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  IdOnΔ Δ σ →
  Δ ∣ Γ ⊢ M ⦂ A →
  substᵀ σ M ≡ M
substᵀ-id-typed hσ (⊢` h) = refl
substᵀ-id-typed hσ (⊢ƛ hA hN) =
  cong₂ ƛ[_]_
    (substᵗ-id-typed hσ hA)
    (substᵀ-id-typed hσ hN)
substᵀ-id-typed hσ (⊢· hL hM) =
  cong₂ _·_
    (substᵀ-id-typed hσ hL)
    (substᵀ-id-typed hσ hM)
substᵀ-id-typed hσ ⊢true = refl
substᵀ-id-typed hσ ⊢false = refl
substᵀ-id-typed hσ ⊢zero = refl
substᵀ-id-typed hσ (⊢suc hM) =
  cong `suc_ (substᵀ-id-typed hσ hM)
substᵀ-id-typed hσ (⊢case hL hM hN) =
  cong₃ case_[zero⇒_|suc⇒_]
    (substᵀ-id-typed hσ hL)
    (substᵀ-id-typed hσ hM)
    (substᵀ-id-typed hσ hN)
substᵀ-id-typed hσ (⊢if hL hM hN) =
  cong₃ `if_then_else
    (substᵀ-id-typed hσ hL)
    (substᵀ-id-typed hσ hM)
    (substᵀ-id-typed hσ hN)
substᵀ-id-typed hσ (⊢Λ hN) =
  cong Λ_ (substᵀ-id-typed (IdOnΔ-exts hσ) hN)
substᵀ-id-typed hσ (⊢·[] hM hB) =
  cong₂ _·[_]
    (substᵀ-id-typed hσ hM)
    (substᵗ-id-typed hσ hB)

substᵀ-id-emptyΔ :
  {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  zero ∣ Γ ⊢ M ⦂ A →
  substᵀ σ M ≡ M
substᵀ-id-emptyΔ hM = substᵀ-id-typed (λ ()) hM

singleTyEnv-suc-cancelᵗ : (A B : Ty) → substᵗ (singleTyEnv A) (renameᵗ suc B) ≡ B
singleTyEnv-suc-cancelᵗ A B =
  trans
    (TS.rename-subst-commute suc (singleTyEnv A) B)
    (trans
      (TS.subst-cong (λ i → refl) B)
      (TS.subst-id B))

singleTyEnv-suc-cancel : (A : Ty) (M : Term)
  → substᵀ (singleTyEnv A) (renameᵀ suc M) ≡ M
singleTyEnv-suc-cancel A M =
  trans
    (substᵀ-renameᵀ-commute suc (singleTyEnv A) M)
    (trans
      (substᵀ-cong (λ i → refl) M)
      (substᵀ-id M))
