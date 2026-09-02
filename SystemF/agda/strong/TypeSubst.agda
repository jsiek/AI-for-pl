module strong.TypeSubst where

-- Algebraic theory of type substitution for Strong System F.
-- Mirrors SystemF/agda/extrinsic/TypeSubst.agda.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Nat using (ℕ; zero; suc)
open import strong.Types

infixr 50 _⨟ᵗ_
_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
(σ₁ ⨟ᵗ σ₂) X = substᵗ σ₂ (σ₁ X)

cons-sub : Ty → Substᵗ → Substᵗ
cons-sub v σ zero    = v
cons-sub v σ (suc Y) = σ Y

subst-one-at-one : Ty → Ty → Ty
subst-one-at-one a b = substᵗ (extsᵗ (singleTyEnv b)) a

single-subst-def : (a b : Ty) → a [ b ]ᵗ ≡ substᵗ (singleTyEnv b) a
single-subst-def a b = refl

subst-one-at-one-def : (a b : Ty) →
  subst-one-at-one a b ≡ substᵗ (extsᵗ (singleTyEnv b)) a
subst-one-at-one-def a b = refl

------------------------------------------------------------------------
-- Congruence helpers
------------------------------------------------------------------------

rename-cong : ∀ {ρ ρ' : Renameᵗ} → ((X : ℕ) → ρ X ≡ ρ' X) → (a : Ty) →
  renameᵗ ρ a ≡ renameᵗ ρ' a
rename-cong h (` X)   = cong `_ (h X)
rename-cong h `ℕ      = refl
rename-cong h `𝔹      = refl
rename-cong h (a ⇒ b) = cong₂ _⇒_ (rename-cong h a) (rename-cong h b)
rename-cong {ρ} {ρ'} h (`∀ a) = cong `∀ (rename-cong h-ext a)
  where
    h-ext : (X : ℕ) → extᵗ ρ X ≡ extᵗ ρ' X
    h-ext zero    = refl
    h-ext (suc X) = cong suc (h X)

subst-cong : ∀ {σ τ : Substᵗ} → ((X : ℕ) → σ X ≡ τ X) → (a : Ty) →
  substᵗ σ a ≡ substᵗ τ a
subst-cong h (` X)   = h X
subst-cong h `ℕ      = refl
subst-cong h `𝔹      = refl
subst-cong h (a ⇒ b) = cong₂ _⇒_ (subst-cong h a) (subst-cong h b)
subst-cong {σ} {τ} h (`∀ a) = cong `∀ (subst-cong h-ext a)
  where
    h-ext : (X : ℕ) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero    = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)

------------------------------------------------------------------------
-- Substitution theorems
------------------------------------------------------------------------

ext-comp : (ρ₁ ρ₂ : Renameᵗ) →
  ((X : ℕ) → extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X' → ρ₂ (ρ₁ X')) X)
ext-comp ρ₁ ρ₂ zero    = refl
ext-comp ρ₁ ρ₂ (suc X) = refl

rename-rename-commute : (ρ₁ ρ₂ : Renameᵗ) → (a : Ty) →
  renameᵗ ρ₂ (renameᵗ ρ₁ a) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) a
rename-rename-commute ρ₁ ρ₂ (` X)   = refl
rename-rename-commute ρ₁ ρ₂ `ℕ      = refl
rename-rename-commute ρ₁ ρ₂ `𝔹      = refl
rename-rename-commute ρ₁ ρ₂ (a ⇒ b) =
  cong₂ _⇒_ (rename-rename-commute ρ₁ ρ₂ a) (rename-rename-commute ρ₁ ρ₂ b)
rename-rename-commute ρ₁ ρ₂ (`∀ a) =
  trans
    (cong `∀ (rename-rename-commute (extᵗ ρ₁) (extᵗ ρ₂) a))
    (cong `∀ (rename-cong (ext-comp ρ₁ ρ₂) a))

exts-ext-comp : (ρ : Renameᵗ) → (τ : Substᵗ) →
  ((X : ℕ) → extsᵗ τ (extᵗ ρ X) ≡ extsᵗ (λ Y → τ (ρ Y)) X)
exts-ext-comp ρ τ zero    = refl
exts-ext-comp ρ τ (suc X) = refl

rename-subst-commute : (ρ : Renameᵗ) → (τ : Substᵗ) → (a : Ty) →
  substᵗ τ (renameᵗ ρ a) ≡ substᵗ (λ X → τ (ρ X)) a
rename-subst-commute ρ τ (` X)   = refl
rename-subst-commute ρ τ `ℕ      = refl
rename-subst-commute ρ τ `𝔹      = refl
rename-subst-commute ρ τ (a ⇒ b) =
  cong₂ _⇒_ (rename-subst-commute ρ τ a) (rename-subst-commute ρ τ b)
rename-subst-commute ρ τ (`∀ a) =
  trans
    (cong `∀ (rename-subst-commute (extᵗ ρ) (extsᵗ τ) a))
    (cong `∀ (subst-cong (exts-ext-comp ρ τ) a))

ext-exts-comp : (ρ : Renameᵗ) → (τ : Substᵗ) →
  ((X : ℕ) → renameᵗ (extᵗ ρ) (extsᵗ τ X) ≡ extsᵗ (λ Y → renameᵗ ρ (τ Y)) X)
ext-exts-comp ρ τ zero    = refl
ext-exts-comp ρ τ (suc Y) =
  trans
    (rename-rename-commute suc (extᵗ ρ) (τ Y))
    (trans
      (rename-cong (λ X → refl) (τ Y))
      (sym (rename-rename-commute ρ suc (τ Y))))

rename-subst : (ρ : Renameᵗ) → (τ : Substᵗ) → (a : Ty) →
  renameᵗ ρ (substᵗ τ a) ≡ substᵗ (λ X → renameᵗ ρ (τ X)) a
rename-subst ρ τ (` X)   = refl
rename-subst ρ τ `ℕ      = refl
rename-subst ρ τ `𝔹      = refl
rename-subst ρ τ (a ⇒ b) =
  cong₂ _⇒_ (rename-subst ρ τ a) (rename-subst ρ τ b)
rename-subst ρ τ (`∀ a) =
  trans
    (cong `∀ (rename-subst (extᵗ ρ) (extsᵗ τ) a))
    (cong `∀ (subst-cong (ext-exts-comp ρ τ) a))

exts-seq : (σ τ : Substᵗ) →
  ((X : ℕ) → ((extsᵗ σ) ⨟ᵗ (extsᵗ τ)) X ≡ extsᵗ (σ ⨟ᵗ τ) X)
exts-seq σ τ zero    = refl
exts-seq σ τ (suc Y) =
  trans
    (rename-subst-commute suc (extsᵗ τ) (σ Y))
    (sym (rename-subst suc τ (σ Y)))

sub-sub : (σ τ : Substᵗ) → (a : Ty) →
  substᵗ τ (substᵗ σ a) ≡ substᵗ (σ ⨟ᵗ τ) a
sub-sub σ τ (` X)   = refl
sub-sub σ τ `ℕ      = refl
sub-sub σ τ `𝔹      = refl
sub-sub σ τ (a ⇒ b) =
  cong₂ _⇒_ (sub-sub σ τ a) (sub-sub σ τ b)
sub-sub σ τ (`∀ a) =
  trans
    (cong `∀ (sub-sub (extsᵗ σ) (extsᵗ τ) a))
    (cong `∀ (subst-cong (exts-seq σ τ) a))

subst-id : (a : Ty) → substᵗ `_ a ≡ a
subst-id (` X)   = refl
subst-id `ℕ      = refl
subst-id `𝔹      = refl
subst-id (a ⇒ b) = cong₂ _⇒_ (subst-id a) (subst-id b)
subst-id (`∀ a)  = trans (cong `∀ (subst-cong exts-var a)) (cong `∀ (subst-id a))
  where
    exts-var : (X : ℕ) → extsᵗ `_ X ≡ ` X
    exts-var zero    = refl
    exts-var (suc X) = refl

------------------------------------------------------------------------
-- The two substitution-commutation laws used pervasively in the metatheory
------------------------------------------------------------------------

-- (a [ b ]ᵗ) [ c ]ᵗ = (subst-one-at-one a c) [ (b [ c ]ᵗ) ]ᵗ
substitution : {a b c : Ty} →
  (a [ b ]ᵗ) [ c ]ᵗ ≡ (subst-one-at-one a c) [ (b [ c ]ᵗ) ]ᵗ
substitution {a} {b} {c} =
  trans
    (trans
      (cong (λ t → t [ c ]ᵗ) (single-subst-def a b))
      (trans
        (single-subst-def (substᵗ σ a) c)
        (sub-sub σ τ a)))
    (trans
      (subst-cong env-eq a)
      (trans
        (sym (sub-sub (extsᵗ τ) φ a))
        (sym
          (trans
            (cong (λ t → t [ (b [ c ]ᵗ) ]ᵗ) (subst-one-at-one-def a c))
            (trans
              (cong (λ t → (substᵗ (extsᵗ τ) a) [ t ]ᵗ) (single-subst-def b c))
              (single-subst-def (substᵗ (extsᵗ τ) a) (substᵗ τ b)))))))
  where
    σ : Substᵗ
    σ = singleTyEnv b

    τ : Substᵗ
    τ = singleTyEnv c

    φ : Substᵗ
    φ = singleTyEnv (substᵗ τ b)

    env-eq : (X : ℕ) → (σ ⨟ᵗ τ) X ≡ ((extsᵗ τ) ⨟ᵗ φ) X
    env-eq zero          = refl
    env-eq (suc zero)    =
      trans
        (sym (subst-id c))
        (trans
          (subst-cong (λ X → refl) c)
          (sym (rename-subst-commute suc φ c)))
    env-eq (suc (suc X)) = refl

exts-sub-cons : {σ : Substᵗ} {a v : Ty} →
  (substᵗ (extsᵗ σ) a) [ v ]ᵗ ≡ substᵗ (cons-sub v σ) a
exts-sub-cons {σ} {a} {v} =
  trans
    (single-subst-def (substᵗ (extsᵗ σ) a) v)
    (trans
      (sub-sub (extsᵗ σ) φ a)
      (subst-cong env-eq a))
  where
    φ : Substᵗ
    φ = singleTyEnv v

    ψ : Substᵗ
    ψ = cons-sub v σ

    env-eq : (X : ℕ) → ((extsᵗ σ) ⨟ᵗ φ) X ≡ ψ X
    env-eq zero    = refl
    env-eq (suc Y) =
      trans
        (rename-subst-commute suc φ (σ Y))
        (trans
          (subst-cong (λ X → refl) (σ Y))
          (subst-id (σ Y)))

rename-[]ᵗ-commute : (ρ : Renameᵗ) (A B : Ty) →
  renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
rename-[]ᵗ-commute ρ A B =
  trans
    (trans
      (cong (renameᵗ ρ) (single-subst-def A B))
      (rename-subst ρ (singleTyEnv B) A))
    (trans
      (subst-cong env-eq A)
      (sym (rename-subst-commute (extᵗ ρ) (singleTyEnv (renameᵗ ρ B)) A)))
  where
    env-eq : (X : ℕ) →
      (λ Y → renameᵗ ρ (singleTyEnv B Y)) X ≡
      (λ Y → singleTyEnv (renameᵗ ρ B) (extᵗ ρ Y)) X
    env-eq zero    = refl
    env-eq (suc X) = refl

subst-[]ᵗ-commute : (σ : Substᵗ) (A B : Ty) →
  substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
subst-[]ᵗ-commute σ A B =
  trans
    (cong (λ T → substᵗ σ T) (single-subst-def A B))
    (trans
      (sub-sub (singleTyEnv B) σ A)
      (trans
        (subst-cong env-eq A)
        (sym (exts-sub-cons {σ = σ} {a = A} {v = substᵗ σ B}))))
  where
    env-eq : (X : ℕ) → ((singleTyEnv B) ⨟ᵗ σ) X ≡ cons-sub (substᵗ σ B) σ X
    env-eq zero    = refl
    env-eq (suc X) = refl
