module strong-rep-store.Progress where

-- File Charter:
--   * THE PUBLIC PROGRESS SURFACE, AND NOTHING ELSE.  §1 states
--     `Progress` explicitly: from `Δ ∣ [] ⊢ M ⦂ A` alone, M is a
--     `Value` or there is an `M′` with `Δ ⊢ M -→ M′`.  The statement is
--     PREMISE-FREE — no `WfCtx Δ`, unlike preservation — because every
--     boundary typing node carries its own `BoundaryWf`, so the induction
--     never needs a global one.  §2 supplies the theorem outright,
--     `progress = strong-rep-store.proof.Progress.Impl.progress`.  It is
--     UNCONDITIONAL as of 2026-09-21: the merged-frame reading is proved
--     by `strong-rep-store.Boundary.merged-conversion-exists`.
--   * NO PROOF SCRIPT AND NO CANONICAL-FORMS SUITE HERE.  Those are
--     strong-rep-store.proof.Progress and strong-rep-store.proof.Canonical. 
-- Preservation
--     is strong-rep-store.Preservation; the composition of the two is
--     strong-rep-store.TypeSafety.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ)
open import strong-rep-store.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong-rep-store.Reduction using (_⊢_-→_)
import strong-rep-store.proof.Progress as P

------------------------------------------------------------------------
-- 1. Public statement
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))

------------------------------------------------------------------------
-- 2. The theorem
------------------------------------------------------------------------

progress : Progress
progress = P.Impl.progress
