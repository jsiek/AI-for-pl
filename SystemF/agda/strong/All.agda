module strong.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

-- the core
open import strong.Types
open import strong.TypeSubst
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

-- executable, derivation-producing type checking, and the step function
-- that searches for a redex.  Neither depends on the metatheory below, so
-- both are checked here, before it.
open import strong.TypeCheck
open import strong.Eval
open import strong.notes.RepresentationReductionExamples
open import strong.notes.ReUnlockWall
open import strong.notes.ForallPayloadWall
open import strong.notes.CrossingAudit
open import strong.notes.CancelRReachabilityWitness
open import strong.notes.RawRunProbe
open import strong.notes.PeelPremise

-- the main theorems
open import strong.Preservation
open import strong.TypeSafety

-- the proof scripts
open import strong.proof.Preserve
open import strong.proof.PeelDual
open import strong.proof.RepWeaken
open import strong.proof.MoveScope
open import strong.proof.TypeSafety

-- THE CANCELR WALL AND ITS REPAIR (2026-09-19).  This one notes module
-- sits BELOW the proof scripts rather than with the others above, because
-- its §6 retypes the wall's own contractum with
-- `strong.proof.MoveScope.preserve-CancelR` — the preservation case the
-- repaired rule generates.
open import strong.notes.CancelRShiftWall

-- THE REP-WEAKENING WALL AND ITS REPAIR (2026-09-20).  The simplified
-- `RepWeakenTyping` was FALSE without a well-formed bind block: the
-- weakened context has to be a `WfCtx`, because a boundary inside the
-- crossing argument stores one.  The premise `reps Δ ⊢ᴮ Rs` repairs it,
-- it is free at the one call site, and with it the statement is proved
-- (strong.proof.RepWeaken).
open import strong.notes.RepWeakenBindsWall

-- THE ADDLOCK0 WALL (2026-09-20).  `AddLock0Typing` is FALSE, and no
-- premise repairs it: `TyPeelR-⟪⟫` re-spells the moved boundary's
-- conversion with `renᶜ suc`, which is right for the INTERIOR reading and
-- wrong for the CONVERSION reading — the latter SKIPS the appended lock,
-- so the new ordinary name is displaced by the moved morphism's own
-- unlocks.  The module runs a closed, plain System F program that loses
-- its type at that step, and proves the reached state untypeable; hence
-- `¬ Preservation`.  It sits here because it reads `strong.Preservation`.
open import strong.notes.AddLock0Wall

-- progress (the canonical-forms suite, the proof script, the theorem)
open import strong.proof.Canonical
open import strong.proof.Progress
open import strong.Progress

-- THE SOUNDNESS GATE.  A conceal must cite a REPRESENTED binder, and the
-- two-universe design refuses it twice over: the name may be absent from
-- the map, or the representation variable it names may be `abstR`.
open import strong.proof.Adversary

-- THE ID-LAYER FACTS.  What makes IdPush and CancelR legitimate: the
-- pushed name is already written in the inner conversion (one universe
-- up, on the representation variable), `unseal` is the only active
-- conversion an id-layer can meet, and the naked drop is unsound except
-- at an empty frame.
open import strong.proof.IdLayer

-- CANONICITY.  Every conversion reduction writes is in the canonical
-- family, and the family survives reduction — including `Peel`'s
-- re-spelling onto the dual's name map, which is what the two universes
-- added.
open import strong.proof.Canonicity

-- THE SHIFT AUDIT (2026-09-08, ported 2026-09-19).  Every rule that MOVES
-- a subterm, checked against frame exactness — now the relational
-- transport lemmas of strong.CtxMorph §3a plus the observation that every
-- move but TyBeta's is REPRESENTATION-ONLY — together with the tower
-- measure that makes the wrapper clause of TyPeelR terminate.
open import strong.proof.ShiftAudit

-- THE LIVING REGRESSION AND THE RENDERER (ported 2026-09-19, closing the
-- frontier).  `strong.Examples` is closed programs, their runs, their
-- typings and the refutations that still hold, stated through
-- `TypeCheck.agda`/`Eval.agda` rather than by hand-written boundary
-- derivations; `strong.Show` renders de Bruijn terms with names, printing
-- the two universes differently (X names α) and a whole run with the rule
-- that fired at each step.
open import strong.Examples
open import strong.Show
