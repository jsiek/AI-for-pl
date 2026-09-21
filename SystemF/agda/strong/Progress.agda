module strong.Progress where

-- File Charter:
--   * THE PUBLIC PROGRESS SURFACE, AND NOTHING ELSE.  §1 states
--     `Progress` explicitly: from `Δ ∣ [] ⊢ M ⦂ A` alone, M is a
--     `Value` or there is an `M′` with `Δ ⊢ M -→ M′`.  The statement is
--     PREMISE-FREE — no `WfCtx Δ`, unlike preservation — because every
--     boundary typing node carries its own `MorphWf`, so the induction
--     never needs a global one.  §2 supplies the theorem outright,
--     `progress = strong.proof.Progress.Impl.progress`.  It is
--     UNCONDITIONAL as of 2026-09-21: the merged-frame reading is proved
--     by `strong.CtxMorph.merged-conversion-exists`.
--   * NO PROOF SCRIPT AND NO CANONICAL-FORMS SUITE HERE.  Those are
--     strong.proof.Progress and strong.proof.Canonical.  Preservation
--     is strong.Preservation; the composition of the two is
--     strong.TypeSafety.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_)
import strong.proof.Progress as P

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
