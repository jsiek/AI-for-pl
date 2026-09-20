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
-- What remains a parameter is exactly
--
--   * the representation-only transport `AddLock0Typing` — and since
--     2026-09-20 that parameter is KNOWN FALSE.
--
-- PRESERVATION IS FALSE AS THE RULES STAND (2026-09-20).
-- `strong.notes.AddLock0Wall` refutes `AddLock0Typing` and, at the same
-- instance, `Preservation` and `Preservation*` below: a closed, plain
-- System F program — no hand-written boundary — loses its type three
-- steps in, at `TyPeelR-⟪⟫`.  That rule re-spells the moved boundary's
-- conversion with `renᶜ suc`, the renaming that is correct for the
-- INTERIOR reading (where `addLock0`'s appended lock, acting first,
-- deletes the new ordinary name) and wrong for the CONVERSION reading
-- (which SKIPS locks, so the new name survives and the moved morphism's
-- own unlocks displace it).  No premise repairs a contractum; the rule
-- needs the repair `Peel` got on 2026-09-18 — name the moved conversion
-- and carry a `SameConv`.  `Stage1` below is therefore a conditional
-- theorem with a refuted hypothesis, kept so that the assembled proof
-- survives the rule repair.
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
-- 2. The parameterized theorem
------------------------------------------------------------------------

module Stage1
  (addLock0  : P.AddLock0Typing)
  where

  private
    module I = P.Impl RW.cross-Λ-⊢ addLock0
                      (PD.preserve-Peel RW.rep-weaken-⊢)
                      MS.preserve-CancelR
                      MS.preserve-IdPush

  preservation : Preservation
  preservation = I.preserve

  preservation* : Preservation*
  preservation* = I.preserve*
