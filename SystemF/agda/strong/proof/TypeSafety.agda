module strong.proof.TypeSafety where

-- TYPE SAFETY for Strong System F: the composition of progress and
-- preservation along a run.  The two theorems are stage-1 parameterized
-- (strong.Progress, strong.Preservation), so their composition inherits
-- every parameter of both: `MergedReading` from progress, and the three
-- representation transports from preservation.  `CancelRCase` is no
-- longer among them: the rule repair of 2026-09-19 made it provable, and
-- `strong.proof.MoveScope.preserve-CancelR` proves it.  The public
-- statement lives in strong.TypeSafety.
--
-- The `WfCtx Δ` premise is preservation's (see notes/DECISIONS.md,
-- 2026-09-18): progress needs none, but safety retypes every state the
-- run reaches, and retyping is what a duplicate name map breaks.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; WfCtx)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_)
import strong.proof.Preserve as P
import strong.proof.Progress as PP
import strong.Progress as Pr
import strong.Preservation as Pv

-- A well-typed closed term at a well-formed context, after any number of
-- steps, is a value or can step again — it never gets stuck.
TypeSafety : Set
TypeSafety = ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* N
  → Value N ⊎ (Σ[ N′ ∈ Term ] (Δ ⊢ N -→ N′))

module Stage1
  (merged-reading : PP.MergedReading)
  (crossΛ    : P.CrossΛTyping)
  (addLock0  : P.AddLock0Typing)
  (repWeaken : P.RepWeakenTyping)
  where

  private
    module Pr1 = Pr.Stage1 merged-reading
    module Pv1 = Pv.Stage1 crossΛ addLock0 repWeaken

  type-safety : TypeSafety
  type-safety wfΔ ⊢M M-→*N =
    Pr1.progress (Pv1.preservation* wfΔ ⊢M M-→*N)
