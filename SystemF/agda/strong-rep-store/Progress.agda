module strong-rep-store.Progress where

-- File Charter:
--   * THE PUBLIC PROGRESS SURFACE, AND NOTHING ELSE.  §1 states
--     `Progress`: from `Δ ∣ [] ⊢ M ⦂ A` alone, M is a `Value` or there
--     are an `M′` and a store change `δ` with `Δ ⊢ M -→ M′ ∣ δ`.  The
--     statement is PREMISE-FREE — every boundary typing node carries
--     its own `BoundaryWf`.  §2 supplies the theorem outright.
--   * THE CHANGE IS EXISTENTIALLY QUANTIFIED: `det` says the pair
--     `(M′ , δ)` is unique, `preservation` types the contractum at
--     `apply δ Δ`.
--   * NO PROOF SCRIPT AND NO CANONICAL-FORMS SUITE HERE.
-- Commentary: Commentary.md § Progress.agda

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ; Alloc)
open import strong-rep-store.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong-rep-store.Reduction using (_⊢_-→_∣_)
import strong-rep-store.proof.Progress as P

------------------------------------------------------------------------
-- 1. Public statement
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))

------------------------------------------------------------------------
-- 2. The theorem
------------------------------------------------------------------------

progress : Progress
progress = P.Impl.progress
