module TypeSubst where

-- File Charter:
--   * Public type-substitution support for PolyNuBar.
--   * Re-exports the core type syntax plus parallel renaming/substitution.
--   * Provides small congruence/composition helpers used by later proofs.

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Types public

infixr 50 _⨟ᵗ_
_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
(σ ⨟ᵗ τ) X = substᵗ τ (σ X)

substᵗ-cong :
  ∀ {σ τ : Substᵗ} →
  ((X : Var) → σ X ≡ τ X) →
  (A : Ty) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (` X) = h X
substᵗ-cong h (`ι ι) = refl
substᵗ-cong h ★ = refl
substᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong h (A `× B) = cong₂ _`×_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ} {τ} h (`∀ A) = cong `∀_ (substᵗ-cong h′ A)
  where
  h′ : (X : Var) → extsᵗ σ X ≡ extsᵗ τ X
  h′ zero = refl
  h′ (suc X) = cong ⇑ᵗ (h X)

renameᵗ-cong :
  ∀ {ρ ρ′ : Renameᵗ} →
  ((X : Var) → ρ X ≡ ρ′ X) →
  (A : Ty) →
  renameᵗ ρ A ≡ renameᵗ ρ′ A
renameᵗ-cong h (` X) = cong `_ (h X)
renameᵗ-cong h (`ι ι) = refl
renameᵗ-cong h ★ = refl
renameᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (renameᵗ-cong h A) (renameᵗ-cong h B)
renameᵗ-cong h (A `× B) = cong₂ _`×_ (renameᵗ-cong h A) (renameᵗ-cong h B)
renameᵗ-cong {ρ} {ρ′} h (`∀ A) = cong `∀_ (renameᵗ-cong h′ A)
  where
  h′ : (X : Var) → extᵗ ρ X ≡ extᵗ ρ′ X
  h′ zero = refl
  h′ (suc X) = cong suc (h X)

single-subst-def : (A B : Ty) → A [ B ]ᵗ ≡ substᵗ (singleTyEnv B) A
single-subst-def A B = refl
