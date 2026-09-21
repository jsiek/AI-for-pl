module strong-rep-var.Preservation where

-- File Charter:
--   * THE PUBLIC PRESERVATION SURFACE, AND NOTHING ELSE.  §1 states
--     `Preservation` and `Preservation*` explicitly; §2 proves them as
--     `preservation` and `preservation*`.  Both are UNCONDITIONAL
--     THEOREMS as of 2026-09-20 — no `Stage1` module, no parameter.
--     Each takes `WfCtx Δ`, a typing `Δ ∣ [] ⊢ M ⦂ A` and a step
--     (respectively a `-→*` run), and returns `Δ ∣ [] ⊢ M′ ⦂ A`.
--   * NO PROOF SCRIPT LIVES HERE.  The two theorems are thin wrappers
--     around `strong-rep-var.proof.Preserve.Impl`, instantiated with
--     `RepWeaken.cross-Λ-⊢`, `AddLock0.addLock0-⊢`,
--     `PeelDual.preserve-Peel RepWeaken.rep-weaken-⊢`,
--     `MoveScope.preserve-CancelR` and `MoveScope.preserve-IdPush`.
--     Progress is strong-rep-var.Progress, their composition is
--     strong-rep-var.TypeSafety, and the refuted statements that shaped these
--     rules are the wall modules under notes/.
--   * WHY `WfCtx Δ` IS PART OF THE STATEMENT — the premise-free form is
--     FALSE here (notes/DECISIONS.md, 2026-09-18).  The reduction
--     relation is indexed by the type context Δ alone, the term context
--     being empty; but a contractum can MINT a `BoundaryWf`, whose
--     exterior field demands `WfCtx Δ`, from a redex that mentioned no
--     ordinary type variable at all.  The counterexample is spelled out
--     below.  `progress` needs no such premise, because every boundary
--     typing node carries its own `BoundaryWf`.
--
-- HOW THE THREE CROSSING CASES LANDED.  Stage 2
-- (2026-09-19) discharged ALL THREE: `IdPush` and, after
-- the `CancelR` rule repair of the same day, `CancelR` are proved
-- outright (strong-rep-var.proof.MoveScope), and `Peel` is proved in
-- strong-rep-var.proof.PeelDual — UNCONDITIONALLY since 2026-09-20, when
-- `RepWeakenTyping` was proved (`strong-rep-var.proof.RepWeaken.rep-weaken-⊢`,
-- on the statement repaired that day with the premise `reps Δ ⊢ᴮ Rs`).
-- NOTHING REMAINS A PARAMETER (2026-09-20).  The last one,
-- `AddLock0Typing`, is proved by `strong-rep-var.proof.AddLock0.addLock0-⊢`,
-- so
-- `preservation` and `preservation*` below are UNCONDITIONAL theorems.
--
-- THE WALL OF 2026-09-20, AND ITS REPAIR.  `strong-rep-var.notes.AddLock0Wall`
-- refuted the OLD `AddLock0Typing` and, at the same instance, `Preservation`
-- and `Preservation*` below: a closed, plain System F program — no
-- hand-written boundary — lost its type three steps in, at `TyPeelR-⟪⟫`.
-- That rule re-spelled the moved boundary's conversion with `renᶜ suc`, the
-- renaming that is correct for the INTERIOR reading (where `addLock0`'s
-- appended lock, acting first, deletes the new ordinary name) and wrong for
-- the CONVERSION reading (which SKIPS locks, so the new name survives and
-- the moved boundary scope's own unlocks displace it).  No premise repairs a
-- contractum, so the RULE was repaired, with Jeremy's approval and in the
-- pattern `Peel` got on 2026-09-18: the moved conversion is NAMED and
-- pinned by a `SameConv`, against the old conversion context viewed through
-- the representation renaming the inserted binder makes.  The wall's
-- program now runs to a value in four steps with every state typed, and the
-- wall module refutes only its own LOCAL copy of the retired statement.
--
-- `AddLock0Typing` in that reshaped form IS PROVED, the same day
-- (`strong-rep-var.proof.AddLock0`): the `env`-to-`env` transport across one
-- inserted representation binder and one fresh ordinary name, with the
-- moved conversion supplied by the rule.  The `Stage1` module that carried
-- it is gone; the theorems below are stated outright.
--
-- `CrossΛTyping` was proved on 2026-09-20 by
-- `strong-rep-var.proof.RepWeaken.cross-Λ-⊢`, so Beta substitution is now
-- unconditional too.
-- `CancelRCase` is no longer among them.  It WAS refuted — the old rule
-- re-spelled the inner layer's identity type in the OUTER conversion
-- context and so dropped the `numBinds Θ₁` shift that `env` demands, at a
-- redex reachable from a closed plain source program.  Repair (a) was
-- approved by Jeremy on 2026-09-19 and installed in
-- `strong-rep-var.Reduction`:
-- the premise now reads the cancelled seal's own source at Θ₁'s
-- conversion context.  `strong-rep-var.proof.MoveScope.preserve-CancelR`
-- proves
-- the repaired case outright, so `Stage1` no longer takes a `cancel`
-- parameter.
--
-- `WfCtx Δ` is now part of the statement.  For example, let `names Δ` be
-- `0 ∷ 0 ∷ []`.  The redex
--
--     (Λ ($ 0)) ·[ `ℕ , `ℕ ]
--
-- can be typed because it mentions no ordinary type variable.  TyBeta's
-- contractum, however, contains a newly minted `BoundaryWf`, whose exterior
-- field requires `WfCtx Δ`; uniqueness fails for that duplicate name map.

open import Data.List using ([])

open import strong-rep-var.Ctx using (Ctxᵗ; WfCtx)
open import strong-rep-var.Terms using (_∣_⊢_⦂_)
open import strong-rep-var.Reduction using (_⊢_-→_; _⊢_-→*_)

import strong-rep-var.proof.Preserve as P
import strong-rep-var.proof.PeelDual as PD
import strong-rep-var.proof.MoveScope as MS
import strong-rep-var.proof.RepWeaken as RW
import strong-rep-var.proof.AddLock0 as AL

------------------------------------------------------------------------
-- 1. Public statements
------------------------------------------------------------------------

Preservation : Set
Preservation = ∀ {Δ M M′ A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′
  → Δ ∣ [] ⊢ M′ ⦂ A

Preservation* : Set
Preservation* = ∀ {Δ M M′ A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* M′
  → Δ ∣ [] ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- 2. The theorems
------------------------------------------------------------------------

private
  module I = P.Impl RW.cross-Λ-⊢ AL.addLock0-⊢
                    (PD.preserve-Peel RW.rep-weaken-⊢)
                    MS.preserve-CancelR
                    MS.preserve-IdPush

preservation : Preservation
preservation = I.preserve

preservation* : Preservation*
preservation* = I.preserve*
