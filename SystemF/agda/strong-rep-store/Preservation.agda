module strong-rep-store.Preservation where

-- File Charter:
--   * THE PUBLIC PRESERVATION SURFACE, AND NOTHING ELSE.  §1 states
--     `Preservation`, `PreservationWf` and `Preservation*` explicitly;
--     §2 proves them as `preservation`, `preservation-wf` and
--     `preservation*`.  All three are UNCONDITIONAL THEOREMS — no
--     `Stage1` module, no parameter.  Each takes `WfCtx Δ`, a typing
--     `Δ ∣ [] ⊢ M ⦂ A` and a step (respectively a `-→*` run).
--   * A STEP RETURNS THE CHANGE IT MADE TO THE STORE (experiment 2,
--     notes/RepStoreSketch.md).  So the contractum is typed at
--     `apply δ Δ`, not at Δ: a ∀-elimination ALLOCATES the cell for the
--     type argument's representation at index 0 and pushes every
--     existing representation variable up by one.  `PreservationWf` is
--     the companion that keeps the context well formed, and it is what
--     `preservation*` threads along a run; the run's final context is
--     read off the derivation by `runCtx` (strong-rep-store.Reduction).
--   * NO PROOF SCRIPT LIVES HERE.  The theorems are thin wrappers around
--     `strong-rep-store.proof.Preserve.Impl` and `preserve-wf`,
--     instantiated with `RepWeaken.cross-Λ-⊢`, `AddLock0.addLock0-⊢`,
--     `RepWeaken.shift-⊢` (THE SIBLING SHIFT), `PeelDual.preserve-Peel`,
--     `MoveScope.preserve-CancelR` and `MoveScope.preserve-IdPush`.
--     Progress is strong-rep-store.Progress, their composition is
--     strong-rep-store.TypeSafety, and the refuted statements that shaped
--     these rules are the wall modules under notes/.
--   * WHY `WfCtx Δ` IS PART OF THE STATEMENT — the premise-free form is
--     FALSE here (notes/DECISIONS.md, 2026-09-18).  The reduction
--     relation is indexed by the type context Δ alone, the term context
--     being empty; but a contractum can MINT a `BoundaryWf`, whose
--     exterior field demands `WfCtx Δ`, from a redex that mentioned no
--     ordinary type variable at all.  The counterexample is spelled out
--     below.  `progress` needs no such premise, because every boundary
--     typing node carries its own `BoundaryWf`.
--
-- WHAT THE STORE CHANGED IN THE PROOF (2026-09-22).  One lemma is new
-- and several are gone.  NEW: the SIBLING SHIFT `ShiftTyping`, today's
-- representation weakening at `ρ = suc`
-- (`strong-rep-store.proof.RepWeaken.shift-⊢`), applied in the four
-- congruences to the sibling the redex leaves behind; and `step-alloc`,
-- which reads off a step what it did to the store.  GONE: the
-- `RepWeakenTyping` parameter `Peel` used to consume — `dual-interior`
-- now lands the crossing argument at the exterior ITSELF, so it moves
-- verbatim — and every `shiftBy`/`shiftRep`/`numBinds` occurrence in
-- `TyBeta`, both `TyPeelR` clauses, `CancelR` and `IdPush`.
--
-- HOW THE THREE CROSSING CASES LANDED.  Stage 2 (2026-09-19) discharged
-- all three: `IdPush` and, after the `CancelR` rule repair of the same
-- day, `CancelR` are proved outright
-- (strong-rep-store.proof.MoveScope), and `Peel` is proved in
-- strong-rep-store.proof.PeelDual.  NOTHING REMAINS A PARAMETER
-- (2026-09-20): the last one, `AddLock0Typing`, is proved by
-- `strong-rep-store.proof.AddLock0.addLock0-⊢`.
--
-- THE WALL OF 2026-09-20, AND ITS REPAIR.
-- `strong-rep-store.notes.AddLock0Wall`
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
-- the representation renaming the allocation makes.
--
-- `CancelRCase` WAS refuted too — the old rule re-spelled the inner
-- layer's identity type in the OUTER conversion context and so dropped
-- the `numBinds Θ₁` shift that `env` demanded, at a redex reachable from
-- a closed plain source program.  Repair (a) was approved by Jeremy on
-- 2026-09-19 and installed in `strong-rep-store.Reduction`: the premise
-- now reads the cancelled seal's own source at Θ₁'s conversion context.
-- With the store there is no shift left to drop, but the premise stays —
-- it is a different NAME MAP, which is what `_⊢_≈_⊣_` is for.
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
