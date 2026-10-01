module proof.Types where

-- File Charter:
--   * (GTNF) FORKED FROM strong-rep-nu.proof.Types; ★ clauses added.
--   * THE LEMMAS ABOUT `renameᵗ` AND `substᵗ` the two-universe layer
--     needs: `substᵗ-cong`, `extsᵗ-renᵗ`, `substᵗ-renᵗ`.
--   * NOT THE DEFINITIONS (Types) and not the full
--     algebraic theory (proof.TypeSubst).
--   * IT IS THE BOTTOM OF THE HIERARCHY: it imports
--     Types and the standard library and NOTHING
--     else.  Keep that import list closed when adding a lemma.
-- Commentary (νF): SystemF/agda/strong-rep-nu/Commentary.md § proof/Types.agda

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Types

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
substᵗ-cong h ★       = refl
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
substᵗ-renᵗ ρ ★       = refl
substᵗ-renᵗ ρ (A ⇒ B) = cong₂ _⇒_ (substᵗ-renᵗ ρ A) (substᵗ-renᵗ ρ B)
substᵗ-renᵗ ρ (`∀ A)  =
  cong `∀
    (trans (substᵗ-cong (extsᵗ-renᵗ ρ) A)
           (substᵗ-renᵗ (extᵗ ρ) A))
