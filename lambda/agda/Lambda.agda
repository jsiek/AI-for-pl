module Lambda where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- 1. Syntax
------------------------------------------------------------------------

infix  6 ƛ_
infix  6 ′_
infixl 7 _·_

data Term : Set where
  ′_ : Nat → Term
  ƛ_ : Term → Term
  _·_ : Term → Term → Term

------------------------------------------------------------------------
-- 2. Renaming and parallel substitution
------------------------------------------------------------------------

Rename : Set
Rename = Nat → Nat

Subst : Set
Subst = Nat → Term

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ (′ i) = ′ (ρ i)
rename ρ (ƛ n) = ƛ (rename (ext ρ) n)
rename ρ (l · m) = rename ρ l · rename ρ m

exts : Subst → Subst
exts σ zero = ′ zero
exts σ (suc i) = rename suc (σ i)

subst : Subst → Term → Term
subst σ (′ i) = σ i
subst σ (ƛ n) = ƛ (subst (exts σ) n)
subst σ (l · m) = subst σ l · subst σ m

single-env : Term → Subst
single-env m zero = m
single-env m (suc i) = ′ i

infix  8 _[_]
_[_] : Term → Term → Term
N [ M ] = subst (single-env M) N

------------------------------------------------------------------------
-- 3. Values
------------------------------------------------------------------------

data Value : Term → Set where
  v-var : ∀ {i} → Value (′ i)
  v-lam : ∀ {n} → Value (ƛ n)
