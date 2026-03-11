module TypeSubst where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Nat using (ℕ; zero; suc)
open import SystemF

infixr 50 _⨟ᵗ_
_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
_⨟ᵗ_ sigma1 sigma2 i = substᵗ sigma2 (sigma1 i)

cons-sub : Ty → Substᵗ → Substᵗ
cons-sub v sigma zero = v
cons-sub v sigma (suc j) = sigma j

subst-one-at-one : Ty → Ty → Ty
subst-one-at-one a b = substᵗ (extsᵗ (singleTyEnv b)) a

single-subst-def : (a b : Ty) →
  a [ b ]ᵗ ≡ substᵗ (singleTyEnv b) a
single-subst-def a b = refl

subst-one-at-one-def : (a b : Ty) →
  subst-one-at-one a b ≡ substᵗ (extsᵗ (singleTyEnv b)) a
subst-one-at-one-def a b = refl

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

rename-cong : ∀ {rho rho' : Renameᵗ} → ((i : ℕ) → rho i ≡ rho' i) → (a : Ty) →
  renameᵗ rho a ≡ renameᵗ rho' a
rename-cong {rho} {rho'} h (` i) = cong `_ (h i)
rename-cong {rho} {rho'} h `ℕ = refl
rename-cong {rho} {rho'} h (a ⇒ b) = cong₂ _⇒_ (rename-cong h a) (rename-cong h b)
rename-cong {rho} {rho'} h (`∀ a) = cong `∀ (rename-cong h-ext a)
  where
    h-ext : (i : ℕ) → extᵗ rho i ≡ extᵗ rho' i
    h-ext zero = refl
    h-ext (suc i) = cong suc (h i)

subst-cong : ∀ {sigma tau : Substᵗ} → ((i : ℕ) → sigma i ≡ tau i) → (a : Ty) →
  substᵗ sigma a ≡ substᵗ tau a
subst-cong {sigma} {tau} h (` i) = h i
subst-cong {sigma} {tau} h `ℕ = refl
subst-cong {sigma} {tau} h (a ⇒ b) = cong₂ _⇒_ (subst-cong h a) (subst-cong h b)
subst-cong {sigma} {tau} h (`∀ a) = cong `∀ (subst-cong h-ext a)
  where
    h-ext : (i : ℕ) → extsᵗ sigma i ≡ extsᵗ tau i
    h-ext zero = refl
    h-ext (suc i) = cong (renameᵗ suc) (h i)

------------------------------------------------------------------------
-- Converted substitution theorems
------------------------------------------------------------------------

ext-comp : (rho1 rho2 : Renameᵗ) →
  ((i : ℕ) → extᵗ rho2 (extᵗ rho1 i) ≡ extᵗ (λ i' → rho2 (rho1 i')) i)
ext-comp rho1 rho2 zero = refl
ext-comp rho1 rho2 (suc i) = refl

rename-rename-commute : (rho1 rho2 : Renameᵗ) → (a : Ty) →
  renameᵗ rho2 (renameᵗ rho1 a) ≡ renameᵗ (λ i → rho2 (rho1 i)) a
rename-rename-commute rho1 rho2 (` i) = refl
rename-rename-commute rho1 rho2 `ℕ = refl
rename-rename-commute rho1 rho2 (a ⇒ b) =
  cong₂ _⇒_ (rename-rename-commute rho1 rho2 a) (rename-rename-commute rho1 rho2 b)
rename-rename-commute rho1 rho2 (`∀ a) =
  trans
    (cong `∀ (rename-rename-commute (extᵗ rho1) (extᵗ rho2) a))
    (cong `∀ (rename-cong (ext-comp rho1 rho2) a))

exts-ext-comp : (rho : Renameᵗ) → (tau : Substᵗ) →
  ((i : ℕ) → extsᵗ tau (extᵗ rho i) ≡ extsᵗ (λ j → tau (rho j)) i)
exts-ext-comp rho tau zero = refl
exts-ext-comp rho tau (suc i) = refl

rename-subst-commute : (rho : Renameᵗ) → (tau : Substᵗ) → (a : Ty) →
  substᵗ tau (renameᵗ rho a) ≡ substᵗ (λ i → tau (rho i)) a
rename-subst-commute rho tau (` i) = refl
rename-subst-commute rho tau `ℕ = refl
rename-subst-commute rho tau (a ⇒ b) =
  cong₂ _⇒_ (rename-subst-commute rho tau a) (rename-subst-commute rho tau b)
rename-subst-commute rho tau (`∀ a) =
  trans
    (cong `∀ (rename-subst-commute (extᵗ rho) (extsᵗ tau) a))
    (cong `∀ (subst-cong (exts-ext-comp rho tau) a))

ext-exts-comp : (rho : Renameᵗ) → (tau : Substᵗ) →
  ((i : ℕ) → renameᵗ (extᵗ rho) (extsᵗ tau i) ≡ extsᵗ (λ j → renameᵗ rho (tau j)) i)
ext-exts-comp rho tau zero = refl
ext-exts-comp rho tau (suc j) =
  trans
    (rename-rename-commute suc (extᵗ rho) (tau j))
    (trans
      (rename-cong (λ i → refl) (tau j))
      (sym (rename-rename-commute rho suc (tau j))))

rename-subst : (rho : Renameᵗ) → (tau : Substᵗ) → (a : Ty) →
  renameᵗ rho (substᵗ tau a) ≡ substᵗ (λ i → renameᵗ rho (tau i)) a
rename-subst rho tau (` i) = refl
rename-subst rho tau `ℕ = refl
rename-subst rho tau (a ⇒ b) =
  cong₂ _⇒_ (rename-subst rho tau a) (rename-subst rho tau b)
rename-subst rho tau (`∀ a) =
  trans
    (cong `∀ (rename-subst (extᵗ rho) (extsᵗ tau) a))
    (cong `∀ (subst-cong (ext-exts-comp rho tau) a))

exts-seq : (sigma tau : Substᵗ) →
  ((i : ℕ) → ((extsᵗ sigma) ⨟ᵗ (extsᵗ tau)) i ≡ extsᵗ (sigma ⨟ᵗ tau) i)
exts-seq sigma tau zero = refl
exts-seq sigma tau (suc j) =
  trans
    (rename-subst-commute suc (extsᵗ tau) (sigma j))
    (sym (rename-subst suc tau (sigma j)))

sub-sub : (sigma tau : Substᵗ) → (a : Ty) →
  substᵗ tau (substᵗ sigma a) ≡ substᵗ (sigma ⨟ᵗ tau) a
sub-sub sigma tau (` i) = refl
sub-sub sigma tau `ℕ = refl
sub-sub sigma tau (a ⇒ b) =
  cong₂ _⇒_ (sub-sub sigma tau a) (sub-sub sigma tau b)
sub-sub sigma tau (`∀ a) =
  trans
    (cong `∀ (sub-sub (extsᵗ sigma) (extsᵗ tau) a))
    (cong `∀ (subst-cong (exts-seq sigma tau) a))

subst-id : (a : Ty) → substᵗ `_ a ≡ a
subst-id (` i) = refl
subst-id `ℕ = refl
subst-id (a ⇒ b) = cong₂ _⇒_ (subst-id a) (subst-id b)
subst-id (`∀ a) = trans (cong `∀ (subst-cong exts-var a)) (cong `∀ (subst-id a))
  where
    exts-var : (i : ℕ) → extsᵗ `_ i ≡ ` i
    exts-var zero = refl
    exts-var (suc i) = refl

substitution : {a b c : Ty} →
  (a [ b ]ᵗ) [ c ]ᵗ ≡
  (subst-one-at-one a c) [ (b [ c ]ᵗ) ]ᵗ
substitution {a} {b} {c} =
  trans
    (trans
      (cong (λ t → t [ c ]ᵗ) (single-subst-def a b))
      (trans
        (single-subst-def (substᵗ sigma a) c)
        (sub-sub sigma tau a)))
    (trans
      (subst-cong env-eq a)
      (trans
        (sym (sub-sub (extsᵗ tau) phi a))
        (sym
          (trans
            (cong (λ t → t [ (b [ c ]ᵗ) ]ᵗ) (subst-one-at-one-def a c))
            (trans
              (cong (λ t → (substᵗ (extsᵗ tau) a) [ t ]ᵗ) (single-subst-def b c))
              (single-subst-def (substᵗ (extsᵗ tau) a) (substᵗ tau b)))))))
  where
    sigma : Substᵗ
    sigma = singleTyEnv b

    tau : Substᵗ
    tau = singleTyEnv c

    phi : Substᵗ
    phi = singleTyEnv (substᵗ tau b)

    env-eq : (i : ℕ) → (sigma ⨟ᵗ tau) i ≡ ((extsᵗ tau) ⨟ᵗ phi) i
    env-eq zero = refl
    env-eq (suc zero) =
      trans
        (sym (subst-id c))
        (trans
          (subst-cong (λ i → refl) c)
          (sym (rename-subst-commute suc phi c)))
    env-eq (suc (suc k)) = refl

exts-sub-cons : {sigma : Substᵗ} {a v : Ty} →
  (substᵗ (extsᵗ sigma) a) [ v ]ᵗ ≡
  substᵗ (cons-sub v sigma) a
exts-sub-cons {sigma} {a} {v} =
  trans
    (single-subst-def (substᵗ (extsᵗ sigma) a) v)
    (trans
      (sub-sub (extsᵗ sigma) phi a)
      (subst-cong env-eq a))
  where
    phi : Substᵗ
    phi = singleTyEnv v

    psi : Substᵗ
    psi = cons-sub v sigma

    env-eq : (i : ℕ) → ((extsᵗ sigma) ⨟ᵗ phi) i ≡ psi i
    env-eq zero = refl
    env-eq (suc j) =
      trans
        (rename-subst-commute suc phi (sigma j))
        (trans
          (subst-cong (λ i → refl) (sigma j))
          (subst-id (sigma j)))
