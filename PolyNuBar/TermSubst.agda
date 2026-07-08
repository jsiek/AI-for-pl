module TermSubst where

-- File Charter:
--   * Public term-substitution support for PolyNuBar.
--   * Re-exports raw terms and typing, and names the usual parallel
--     substitution composition operation.

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Terms public

infixr 50 _⨟_
_⨟_ : Subst → Subst → Subst
(σ ⨟ τ) x = subst τ (σ x)

ext-cong :
  ∀ {ρ ρ′ : Rename} →
  ((x : Var) → ρ x ≡ ρ′ x) →
  (x : Var) →
  ext ρ x ≡ ext ρ′ x
ext-cong h zero = refl
ext-cong h (suc x) = cong suc (h x)

exts-cong :
  ∀ {σ τ : Subst} →
  ((x : Var) → σ x ≡ τ x) →
  (x : Var) →
  exts σ x ≡ exts τ x
exts-cong h zero = refl
exts-cong h (suc x) = cong (rename suc) (h x)
