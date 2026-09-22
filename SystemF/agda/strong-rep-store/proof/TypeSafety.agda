module strong-rep-store.proof.TypeSafety where

-- TYPE SAFETY for Strong System F: the composition of progress and
-- preservation along a run.  Both component theorems are unconditional:
-- preservation since 2026-09-20, and progress since 2026-09-21, when the
-- last parameter `MergedReading` was proved.  The public statement lives
-- in strong-rep-store.TypeSafety.
--
-- SINCE THE STORE (2026-09-22) THE RUN MOVES THE CONTEXT.  Every step
-- returns the change it made, so the state a run reaches is typed at
-- `runCtx r`, not at Δ, and progress is applied THERE.
--
-- The `WfCtx Δ` premise is preservation's (see notes/DECISIONS.md,
-- 2026-09-18): progress needs none, but safety retypes every state the
-- run reaches, and retyping is what a duplicate name map breaks.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ; WfCtx; Alloc)
open import strong-rep-store.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong-rep-store.Reduction
  using (_⊢_-→_∣_; _⊢_-→*_; runCtx)
import strong-rep-store.Progress as Pr
import strong-rep-store.Preservation as Pv

-- A well-typed closed term at a well-formed context, after any number of
-- steps, is a value or can step again — it never gets stuck.
TypeSafety : Set
TypeSafety = ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
  → Value N ⊎ (Σ[ N′ ∈ Term ] Σ[ δ ∈ Alloc ] (runCtx r ⊢ N -→ N′ ∣ δ))

type-safety : TypeSafety
type-safety wfΔ ⊢M r =
  Pr.progress (Pv.preservation* wfΔ ⊢M r)
