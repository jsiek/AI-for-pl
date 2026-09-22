module strong-rep-store.proof.Types where

-- File Charter:
--   * THE LEMMAS ABOUT `renameᵗ` AND `substᵗ` the two-universe layer
--     needs: `substᵗ-cong`, `extsᵗ-renᵗ`, `substᵗ-renᵗ`.
--   * NOT THE DEFINITIONS (strong-rep-store.Types) and not the full
--     algebraic theory (strong-rep-store.proof.TypeSubst).
--   * IT IS THE BOTTOM OF THE HIERARCHY: it imports
--     strong-rep-store.Types and the standard library and NOTHING
--     else.  Keep that import list closed when adding a lemma.
-- Commentary: Commentary.md § proof/Types.agda

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import strong-rep-store.Types

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
