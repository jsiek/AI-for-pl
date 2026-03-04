module Lambda where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- 1. Syntax
------------------------------------------------------------------------

data Term : Set where
  var : Nat → Term
  lam : Term → Term
  app : Term → Term → Term

------------------------------------------------------------------------
-- 2. Renaming and parallel substitution
------------------------------------------------------------------------

Rename : Set
Rename = Nat → Nat

Subst : Set
Subst = Nat → Term

ext : Rename → Rename
ext rho zero = zero
ext rho (suc i) = suc (rho i)

rename : Rename → Term → Term
rename rho (var i) = var (rho i)
rename rho (lam n) = lam (rename (ext rho) n)
rename rho (app l m) = app (rename rho l) (rename rho m)

exts : Subst → Subst
exts sigma zero = var zero
exts sigma (suc i) = rename suc (sigma i)

subst : Subst → Term → Term
subst sigma (var i) = sigma i
subst sigma (lam n) = lam (subst (exts sigma) n)
subst sigma (app l m) = app (subst sigma l) (subst sigma m)

single-env : Term → Subst
single-env m zero = m
single-env m (suc i) = var i

single-subst : Term → Term → Term
single-subst n m = subst (single-env m) n

------------------------------------------------------------------------
-- 3. Values
------------------------------------------------------------------------

data Value : Term → Set where
  v-var : ∀ {i} → Value (var i)
  v-lam : ∀ {n} → Value (lam n)
