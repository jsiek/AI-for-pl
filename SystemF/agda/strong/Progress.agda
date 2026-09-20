module strong.Progress where

-- File Charter:
--   * THE PUBLIC PROGRESS SURFACE, AND NOTHING ELSE.  §1 states
--     `Progress` explicitly: from `Δ ∣ [] ⊢ M ⦂ A` alone, M is a
--     `Value` or there is an `M′` with `Δ ⊢ M -→ M′`.  The statement is
--     PREMISE-FREE — no `WfCtx Δ`, unlike preservation — because every
--     boundary typing node carries its own `MorphWf`, so the induction
--     never needs a global one.  §2's `Stage1` supplies the theorem,
--     `progress = strong.proof.Progress.Impl.progress`.
--   * NO PROOF SCRIPT AND NO CANONICAL-FORMS SUITE HERE.  Those are
--     strong.proof.Progress and strong.proof.Canonical.  Preservation
--     is strong.Preservation; the composition of the two is
--     strong.TypeSafety.
--   * ONE PARAMETER, AND IT IS DELIBERATE.  `Stage1` abstracts over
--     `strong.proof.Progress.MergedReading`, the merged-frame
--     name-retention invariant.  It is a NEW MAJOR STATEMENT and is
--     held for Jeremy's review rather than proved without approval
--     (notes/DECISIONS.md, 2026-09-19).  It is the ONLY one: the
--     2026-09-20 repair of `TyPeelR-⟪⟫` added no parameter, its
--     moved-boundary reading being proved as
--     `strong.proof.Progress.addLock0-reading`.  Anything that
--     instantiates `Stage1` therefore states that assumption in its own
--     type — do not hide it behind a wrapper.

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
-- 2. Stage-1 parameterized theorem
------------------------------------------------------------------------

module Stage1 (merged-reading : P.MergedReading) where

  private
    module I = P.Impl merged-reading

  progress : Progress
  progress = I.progress
