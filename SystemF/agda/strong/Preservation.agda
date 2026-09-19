module strong.Preservation where

-- Public stage-1 preservation interface for the two-universe design.
--
-- This module intentionally exposes no unconditional theorem yet.  The
-- induction in proof/Preserve is complete once its two representation-only
-- transport facts and the three downstream crossing cases are supplied.
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
-- 2. Stage-1 parameterized theorem
------------------------------------------------------------------------

module Stage1
  (crossΛ   : P.CrossΛTyping)
  (addLock0 : P.AddLock0Typing)
  (peel     : P.PeelCase)
  (cancel   : P.CancelRCase)
  (idpush   : P.IdPushCase)
  where

  private
    module I = P.Impl crossΛ addLock0 peel cancel idpush

  preservation : Preservation
  preservation = I.preserve

  preservation* : Preservation*
  preservation* = I.preserve*
