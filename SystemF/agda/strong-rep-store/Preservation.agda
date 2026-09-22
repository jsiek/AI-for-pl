module strong-rep-store.Preservation where

-- File Charter:
--   * THE PUBLIC PRESERVATION SURFACE, AND NOTHING ELSE.  §1 states
--     `Preservation`, `PreservationWf` and `Preservation*` explicitly;
--     §2 proves them.  All three are UNCONDITIONAL — no parameter.
--   * A STEP RETURNS THE CHANGE IT MADE TO THE STORE, so the
--     contractum is typed at `apply δ Δ`, not at Δ.  `PreservationWf`
--     keeps the context well formed and is what `preservation*`
--     threads along a run, whose final context is `runCtx`.
--   * NO PROOF SCRIPT HERE: these are thin wrappers around
--     strong-rep-store.proof.Preserve.Impl and `preserve-wf`.
--   * WHY `WfCtx Δ` IS PART OF THE STATEMENT: the premise-free form is
--     FALSE — a contractum can mint a `BoundaryWf` whose exterior
--     field demands well-formedness a redex never needed.  `progress`
--     needs no such premise.
-- Commentary: Commentary.md § Preservation.agda

open import Data.List using ([])

open import strong-rep-store.Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import strong-rep-store.Terms using (_∣_⊢_⦂_)
open import strong-rep-store.Reduction
  using (_⊢_-→_∣_; _⊢_-→*_; runCtx)

import strong-rep-store.proof.Preserve as P
import strong-rep-store.proof.PeelDual as PD
import strong-rep-store.proof.MoveScope as MS
import strong-rep-store.proof.RepWeaken as RW
import strong-rep-store.proof.AddLock0 as AL

------------------------------------------------------------------------
-- 1. Public statements
------------------------------------------------------------------------

Preservation : Set
Preservation = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
  → apply δ Δ ∣ [] ⊢ M′ ⦂ A

PreservationWf : Set
PreservationWf = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
  → WfCtx (apply δ Δ)

Preservation* : Set
Preservation* = ∀ {Δ M M′ A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* M′)
  → runCtx r ∣ [] ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- 2. The theorems
------------------------------------------------------------------------

private
  module I = P.Impl RW.cross-Λ-⊢ AL.addLock0-⊢ RW.shift-⊢
                    PD.preserve-Peel
                    MS.preserve-CancelR
                    MS.preserve-IdPush

preservation : Preservation
preservation = I.preserve

preservation-wf : PreservationWf
preservation-wf = P.preserve-wf

preservation* : Preservation*
preservation* = I.preserve*
