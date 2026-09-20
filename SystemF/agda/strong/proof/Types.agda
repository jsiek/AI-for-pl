module strong.proof.Types where

-- Strong System F — lemmas about type renaming and substitution.
--
-- strong.Types holds the definitions; this module holds the equational
-- facts about them.  It sits at the bottom of the hierarchy: it imports
-- strong.Types and the standard library, and nothing else.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import strong.Types

------------------------------------------------------------------------
-- Congruence and rename/subst agreement
------------------------------------------------------------------------

substᵗ-cong : ∀ {σ τ : Substᵗ}
  → ((X : TyVar) → σ X ≡ τ X)
  → (A : Ty)
  → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (` X)   = h X
substᵗ-cong h `ℕ      = refl
substᵗ-cong h `𝔹      = refl
substᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ} {τ} h (`∀ A) = cong `∀ (substᵗ-cong h-ext A)
  where
  h-ext : (X : TyVar) → extsᵗ σ X ≡ extsᵗ τ X
  h-ext zero    = refl
  h-ext (suc X) = cong (renameᵗ suc) (h X)

extsᵗ-renᵗ : (ρ : Renameᵗ) → (X : TyVar)
  → extsᵗ (renᵗ ρ) X ≡ renᵗ (extᵗ ρ) X
extsᵗ-renᵗ ρ zero    = refl
extsᵗ-renᵗ ρ (suc X) = refl

substᵗ-renᵗ : (ρ : Renameᵗ) (A : Ty) → substᵗ (renᵗ ρ) A ≡ renameᵗ ρ A
substᵗ-renᵗ ρ (` X)   = refl
substᵗ-renᵗ ρ `ℕ      = refl
substᵗ-renᵗ ρ `𝔹      = refl
substᵗ-renᵗ ρ (A ⇒ B) = cong₂ _⇒_ (substᵗ-renᵗ ρ A) (substᵗ-renᵗ ρ B)
substᵗ-renᵗ ρ (`∀ A)  =
  cong `∀
    (trans (substᵗ-cong (extsᵗ-renᵗ ρ) A)
           (substᵗ-renᵗ (extᵗ ρ) A))
