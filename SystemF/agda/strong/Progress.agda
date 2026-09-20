module strong.Progress where

-- Public stage-1 progress interface for the two-universe design.
--
-- The logical statement remains premise-free: every boundary typing node
-- carries its own `MorphWf`, so the induction never needs a global `WfCtx Δ`.
-- The proof is complete once the merged-frame name-retention invariant
-- stated as `strong.proof.Progress.MergedReading` is supplied.  That
-- invariant is a new major statement and is deliberately left as a stage-1
-- parameter for review rather than proved here without approval.  It is
-- the ONLY one: the 2026-09-20 repair of `TyPeelR-⟪⟫` added no parameter,
-- its moved-boundary reading being proved as
-- `strong.proof.Progress.addLock0-reading`.

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
