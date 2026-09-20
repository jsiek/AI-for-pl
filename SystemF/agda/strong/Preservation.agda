module strong.Preservation where

-- Public preservation interface for the two-universe design.
--
-- This module intentionally exposes no unconditional theorem.  Stage 2
-- (2026-09-19) discharged ALL THREE crossing cases: `IdPush` and, after
-- the `CancelR` rule repair of the same day, `CancelR` are proved
-- outright (strong.proof.MoveScope), and `Peel` is proved in
-- strong.proof.PeelDual — UNCONDITIONALLY since 2026-09-20, when
-- `RepWeakenTyping` was proved (`strong.proof.RepWeaken.rep-weaken-⊢`,
-- on the statement repaired that day with the premise `reps Δ ⊢ᴮ Rs`).
-- NOTHING REMAINS A PARAMETER (2026-09-20).  The last one,
-- `AddLock0Typing`, is proved by `strong.proof.AddLock0.addLock0-⊢`, so
-- `preservation` and `preservation*` below are UNCONDITIONAL theorems.
--
-- THE WALL OF 2026-09-20, AND ITS REPAIR.  `strong.notes.AddLock0Wall`
-- refuted the OLD `AddLock0Typing` and, at the same instance, `Preservation`
-- and `Preservation*` below: a closed, plain System F program — no
-- hand-written boundary — lost its type three steps in, at `TyPeelR-⟪⟫`.
-- That rule re-spelled the moved boundary's conversion with `renᶜ suc`, the
-- renaming that is correct for the INTERIOR reading (where `addLock0`'s
-- appended lock, acting first, deletes the new ordinary name) and wrong for
-- the CONVERSION reading (which SKIPS locks, so the new name survives and
-- the moved morphism's own unlocks displace it).  No premise repairs a
-- contractum, so the RULE was repaired, with Jeremy's approval and in the
-- pattern `Peel` got on 2026-09-18: the moved conversion is NAMED and
-- pinned by a `SameConv`, against the old conversion context viewed through
-- the representation renaming the inserted binder makes.  The wall's
-- program now runs to a value in four steps with every state typed, and the
-- wall module refutes only its own LOCAL copy of the retired statement.
--
-- `AddLock0Typing` in that reshaped form IS PROVED, the same day
-- (`strong.proof.AddLock0`): the `env`-to-`env` transport across one
-- inserted representation binder and one fresh ordinary name, with the
-- moved conversion supplied by the rule.  The `Stage1` module that carried
-- it is gone; the theorems below are stated outright.
--
-- `CrossΛTyping` was proved on 2026-09-20 by
-- `strong.proof.RepWeaken.cross-Λ-⊢`, so Beta substitution is now
-- unconditional too.
-- `CancelRCase` is no longer among them.  It WAS refuted — the old rule
-- re-spelled the inner layer's identity type in the OUTER conversion
-- context and so dropped the `numBinds Θ₁` shift that `env` demands, at a
-- redex reachable from a closed plain source program.  Repair (a) was
-- approved by Jeremy on 2026-09-19 and installed in `strong.Reduction`:
-- the premise now reads the cancelled seal's own source at Θ₁'s
-- conversion context.  `strong.proof.MoveScope.preserve-CancelR` proves
-- the repaired case outright, so `Stage1` no longer takes a `cancel`
-- parameter.
--
-- `WfCtx Δ` is now part of the statement.  For example, let `names Δ` be
-- `0 ∷ 0 ∷ []`.  The redex
--
--     (Λ ($ 0)) ·[ `ℕ , `ℕ ]
--
-- can be typed because it mentions no ordinary type variable.  TyBeta's
-- contractum, however, contains a newly minted `MorphWf`, whose exterior
-- field requires `WfCtx Δ`; uniqueness fails for that duplicate name map.

open import Data.List using ([])

open import strong.Ctx using (Ctxᵗ; WfCtx)
open import strong.Terms using (_∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_)

import strong.proof.Preserve as P
import strong.proof.PeelDual as PD
import strong.proof.MoveScope as MS
import strong.proof.RepWeaken as RW
import strong.proof.AddLock0 as AL

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
