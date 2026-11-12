module intrinsic-subst.MetaTheory where

-- File Charter:
--   * Public statements of the parametricity results for intrinsically
--     typed System F: the fundamental theorem of the logical relation,
--     termination of closed terms, and two free theorems.
--   * All of them assume `CompatInst` (Parametricity.agda), the
--     compatibility of the logical relation with type application, which
--     needs impredicativity and so is not provable in --safe Agda.  The
--     assumption is a module parameter, so it shows in every statement.
--   * Thin wrappers around intrinsic-subst/proof/{Parametricity,
--     FreeTheorems}.agda.  Progress is in Reduction.agda; preservation
--     holds by construction (reduction relates terms of the same type).

open import Level using (Level; zero)
open import Data.Product using (∃-syntax; _×_)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.Parametricity
open import intrinsic-subst.FreeTheorems
import intrinsic-subst.proof.Parametricity as P
import intrinsic-subst.proof.FreeTheorems as PF

module _ (compat-∙ : CompatInst) where

  private
    module F = P.Fundamental
      (λ {ℓ} {Δ} {Γ} {A} {M} → compat-∙ {ℓ} {Δ} {Γ} {A} {M})
    module FT = PF.FreeTheoremProofs
      (λ {ℓ} {Δ} {Γ} {A} {M} → compat-∙ {ℓ} {Δ} {Γ} {A} {M})

  -- every well-typed term is related to itself
  fundamental : (ℓ : Level) → ∀ {Δ} {Γ : Ctx Δ} {A} (M : Δ ∣ Γ ⊢ A)
    → LogicalRel ℓ M M
  fundamental = F.fundamental

  -- every closed term reduces to a value
  terminate : ∀ {A} (M : ∅ ∣ ∅ ⊢ A) → ∃[ V ] (M —↠ V) × Value V
  terminate = F.terminate

  -- a term of type ∀α. α → α is the identity
  free-theorem-id : ∀ (M : ∅ ∣ ∅ ⊢ `∀ (` Z ⇒ ` Z)) (A : Type ∅)
    (V : ∅ ∣ ∅ ⊢ A)
    → Value V
    → M ∙ A · V —↠ V
  free-theorem-id = FT.free-theorem-id

  -- representation independence: a term of type ∀α. α → (α → α) → α
  -- cannot tell `true`/`neg` from 1/`flip`
  free-theorem-rep :
    ∀ (M : ∅ ∣ ∅ ⊢ `∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z))
    → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        (M ∙ `Bool · `true · neg —↠ V)
      × (M ∙ `Nat · (`suc `zero) · flip —↠ W)
      × R V W v w
  free-theorem-rep = FT.free-theorem-rep
