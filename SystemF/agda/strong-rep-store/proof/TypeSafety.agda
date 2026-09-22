module strong-rep-store.proof.TypeSafety where

-- File Charter:
--   * TYPE SAFETY: progress composed with preservation along a run.
--     Both components are unconditional.  The public statement is
--     strong-rep-store.TypeSafety.
--   * SINCE THE STORE THE RUN MOVES THE CONTEXT: the state a run
--     reaches is typed at `runCtx r`, and progress is applied THERE.
--   * The `WfCtx Δ` premise is preservation's — safety RETYPES every
--     state the run reaches.
-- Commentary: Commentary.md § proof/TypeSafety.agda

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
