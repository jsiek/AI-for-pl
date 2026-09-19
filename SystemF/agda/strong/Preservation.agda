module strong.Preservation where

-- Public preservation interface for the two-universe design.
--
-- This module intentionally exposes no unconditional theorem.  Stage 2
-- (2026-09-19) discharged ALL THREE crossing cases: `IdPush` and, after
-- the `CancelR` rule repair of the same day, `CancelR` are proved
-- outright (strong.proof.MoveScope), and `Peel` is proved modulo the
-- representation-only weakening `RepWeakenTyping`
-- (strong.proof.PeelDual).  What remains a parameter is exactly
--
--   * the two representation-only transports `CrossΛTyping` and
--     `AddLock0Typing`, and the new `RepWeakenTyping`, all three awaiting
--     review.
-- `CancelRCase` is no longer among them.  It WAS refuted — the old rule
-- re-spelled the inner layer's identity type in the OUTER conversion
-- context and so dropped the `numBinds Θ₁` shift that `env` demands, at a
-- redex reachable from a closed plain source program.  Repair (a) was
-- approved by Jeremy on 2026-09-19 and installed in `strong.Reduction`:
-- the premise now reads the cancelled seal's own source at Θ₁'s
-- conversion context.  `strong.proof.MoveScope.preserve-CancelR` proves
-- the repaired case outright, so `Stage1` no longer takes a `cancel`
-- parameter and the remaining three are the representation-only
-- transports awaiting review.
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
  (crossΛ    : P.CrossΛTyping)
  (addLock0  : P.AddLock0Typing)
  (repWeaken : P.RepWeakenTyping)
  where

  private
    module I = P.Impl crossΛ addLock0
                      (PD.preserve-Peel repWeaken)
                      MS.preserve-CancelR
                      MS.preserve-IdPush

  preservation : Preservation
  preservation = I.preserve

  preservation* : Preservation*
  preservation* = I.preserve*
