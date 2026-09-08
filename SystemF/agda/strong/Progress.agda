module strong.Progress where

-- PROGRESS for Strong System F (v2, the conversion-boundary calculus).
--
-- THE STATEMENT (and why it has the shape it has).
--
--   progress : Δ ∣ [] ⊢ M ⦂ A → Value M ⊎ Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′)
--
-- * THE TERM CONTEXT IS EMPTY — as it must be, `_⊢_-→_` carrying no term
--   context (see strong.Preservation for the same point on the other
--   theorem).  At a non-empty Γ a `` ` x `` is neither a value nor a
--   redex, so the theorem is false outright.
--
-- * THE TYPE CONTEXT IS ARBITRARY.  Reduction goes UNDER Λ and under a
--   boundary, so the theorem is used at `unmasked abst ∷ Δ` and at
--   `interior Θ Δ`; nothing about Δ is assumed, and in particular there
--   is no context well-formedness premise.
--
-- THE PROOF is strong.proof.Progress: induction on the typing
-- derivation, with the three ordinary cases decided by the
-- canonical-forms suite (strong.proof.Canonical) and the BOUNDARY case
-- — the whole content — split out there as `progress-env`, which runs
-- the induction hypothesis on the interior and then classifies the
-- conversion by `act-or-inert`, keeping the active branches' own
-- premises.  The TyPeelR SPLIT (`TyPeelR-Λ` / `TyPeelR-⟪⟫`) is decided
-- there by a second `canon-∀`, on the crossed boundary's interior, and
-- the same inversion reads the clauses' conversion-typing premise off
-- the redex's own `env` (`progress-·[]-∀conv`).
--
-- No parameters, no postulates, no holes (--safe).

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_)
import strong.proof.Progress as P

------------------------------------------------------------------------
-- 1.  The statement
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))

------------------------------------------------------------------------
-- 2.  THE THEOREM
------------------------------------------------------------------------

progress : Progress
progress = P.progress
