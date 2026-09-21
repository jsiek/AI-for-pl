module strong-rep-var.proof.Types where

-- File Charter:
--   * THE LEMMAS ABOUT `renameᵗ` AND `substᵗ` that the two-universe
--     layer needs: `substᵗ-cong`, `extsᵗ-renᵗ`, and the agreement of
--     renaming with substitution, `substᵗ-renᵗ`.
--   * NOT THE DEFINITIONS (strong-rep-var.Types), and not the full algebraic
--     theory — composition, `sub-sub`, `substitution`, the `_[_]ᵗ`
--     commutation laws — which is strong-rep-var.proof.TypeSubst.  This module
-- is
--     the private half of strong-rep-var.Types under the repo's public/private
--     split (notes/DECISIONS.md, 2026-09-20).
--   * IT IS THE BOTTOM OF THE HIERARCHY.  It imports strong-rep-var.Types and
--     the standard library and NOTHING else, which is what lets
--     strong-rep-var.Ctx, strong-rep-var.proof.Ctx and strong-rep-var.Boundary
-- stand on it.
--     Keep that import list closed when adding a lemma.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import strong-rep-var.Types

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
