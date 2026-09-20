module strong.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

-- the core
open import strong.Types
open import strong.TypeSubst
open import strong.Ctx
open import strong.CtxMorph
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

-- executable, derivation-producing type checking, and the step function
-- that searches for a redex.  Neither depends on the metatheory below, so
-- both are checked here, before it.
open import strong.TypeCheck
open import strong.Eval

-- the main theorems
open import strong.Preservation

-- progress (the canonical-forms suite, the proof script, the theorem)
open import strong.Progress
open import strong.TypeSafety

-- THE LIVING REGRESSION AND THE RENDERER (ported 2026-09-19, closing the
-- frontier).  `strong.Examples` is closed programs, their runs, their
-- typings and the refutations that still hold, stated through
-- `TypeCheck.agda`/`Eval.agda` rather than by hand-written boundary
-- derivations; `strong.Show` renders de Bruijn terms with names, printing
-- the two universes differently (X names α) and a whole run with the rule
-- that fired at each step.
open import strong.Examples
open import strong.Show

-- THE SOUNDNESS GATE.  A conceal must cite a REPRESENTED binder, and the
-- two-universe design refuses it twice over: the name may be absent from
-- the map, or the representation variable it names may be `abstR`.
-- Direct gate: no top-level module reaches this soundness audit.
open import strong.proof.Adversary

-- THE ID-LAYER FACTS.  What makes IdPush and CancelR legitimate: the
-- pushed name is already written in the inner conversion (one universe
-- up, on the representation variable), `unseal` is the only active
-- conversion an id-layer can meet, and the naked drop is unsound except
-- at an empty frame.
-- Direct gate: no top-level module reaches this id-layer audit.
open import strong.proof.IdLayer

-- CANONICITY.  Every conversion reduction writes is in the canonical
-- family, and the family survives reduction — including `Peel`'s
-- re-spelling onto the dual's name map, which is what the two universes
-- added.
-- Direct gate: no top-level module reaches this canonicity audit.
open import strong.proof.Canonicity

-- THE SHIFT AUDIT (2026-09-08, ported 2026-09-19).  Every rule that MOVES
-- a subterm, checked against frame exactness — now the relational
-- transport lemmas of strong.CtxMorph §3a plus the observation that every
-- move but TyBeta's is REPRESENTATION-ONLY — together with the tower
-- measure that makes the wrapper clause of TyPeelR terminate.
-- Direct gate: no top-level module reaches this shift audit.
open import strong.proof.ShiftAudit

-- The checked notes come last because CancelRShiftWall reaches MoveScope.
open import strong.notes.All
