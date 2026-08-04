module proof.Substitution.Term.TermSubstitutionSyntax where

-- File Charter:
--   * Syntax-only commutation lemmas for term-variable substitution and
--     type-variable renaming/opening on Nu terms.
--   * Provides the reusable transport equations needed by mediated and
--     non-mediated term-substitution proofs.
--   * Kept hole-free and independent of any narrowing relation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import proof.Core.Properties.NuTermProperties using
  ( renameˣ-renameᵗᵐ
  ; renameᵗᵐ-ext-suc-comm
  ; renameᵗᵐ-left-inverse
  )

substˣᵐ-renameᵗᵐ :
  ∀ ρ τ τ′ M →
  (∀ x → τ x ≡ renameᵗᵐ ρ (τ′ x)) →
  substˣᵐ τ (renameᵗᵐ ρ M) ≡ renameᵗᵐ ρ (substˣᵐ τ′ M)
substˣᵐ-renameᵗᵐ ρ τ τ′ (` x) env = env x
substˣᵐ-renameᵗᵐ ρ τ τ′ (ƛ M) env =
  cong ƛ_ (substˣᵐ-renameᵗᵐ ρ (extˢˣ τ) (extˢˣ τ′) M env-ext)
  where
    env-ext : ∀ x → extˢˣ τ x ≡ renameᵗᵐ ρ (extˢˣ τ′ x)
    env-ext zero = refl
    env-ext (suc x) =
      trans (cong (renameˣᵐ suc) (env x))
            (renameˣ-renameᵗᵐ suc ρ (τ′ x))
substˣᵐ-renameᵗᵐ ρ τ τ′ (L · M) env =
  cong₂ _·_ (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
             (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (Λ M) env =
  cong Λ_ (substˣᵐ-renameᵗᵐ (extᵗ ρ) (↑ᵗᵐ τ) (↑ᵗᵐ τ′) M env-↑)
  where
    env-↑ : ∀ x → ↑ᵗᵐ τ x ≡ renameᵗᵐ (extᵗ ρ) (↑ᵗᵐ τ′ x)
    env-↑ x =
      trans (cong ⇑ᵗᵐ (env x))
            (sym (renameᵗᵐ-ext-suc-comm ρ (τ′ x)))
substˣᵐ-renameᵗᵐ ρ τ τ′ (M •) env =
  cong _• (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (ν A L c) env =
  cong (λ L′ → ν (renameᵗ ρ A) L′ (renameᶜ (extᵗ ρ) c))
       (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
substˣᵐ-renameᵗᵐ ρ τ τ′ ($ κ) env = refl
substˣᵐ-renameᵗᵐ ρ τ τ′ (L ⊕[ op ] M) env =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
    (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (M ⟨ c ⟩) env =
  cong (λ M′ → M′ ⟨ renameᶜ ρ c ⟩)
       (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ blame env = refl

substˣᵐ-shift :
  ∀ τ M →
  substˣᵐ (↑ᵗᵐ τ) (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (substˣᵐ τ M)
substˣᵐ-shift τ M = substˣᵐ-renameᵗᵐ suc (↑ᵗᵐ τ) τ M (λ x → refl)

open-shiftᵐ :
  ∀ α M →
  (⇑ᵗᵐ M) [ α ]ᵀ ≡ M
open-shiftᵐ α M = renameᵗᵐ-left-inverse (λ X → refl) M

substˣᵐ-open :
  ∀ τ M α →
  substˣᵐ τ (M [ α ]ᵀ) ≡ (substˣᵐ (↑ᵗᵐ τ) M) [ α ]ᵀ
substˣᵐ-open τ M α =
  substˣᵐ-renameᵗᵐ (singleRenameᵗ α) τ (↑ᵗᵐ τ) M
    (λ x → sym (open-shiftᵐ α (τ x)))
