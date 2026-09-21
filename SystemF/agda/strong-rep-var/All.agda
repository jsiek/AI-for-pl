module strong-rep-var.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

-- the core
open import strong-rep-var.Types
open import strong-rep-var.Ctx
open import strong-rep-var.Boundary
open import strong-rep-var.Conversion
open import strong-rep-var.Terms
open import strong-rep-var.TermSubst
open import strong-rep-var.Reduction

-- executable, derivation-producing type checking, and the step function
-- that searches for a redex.  Neither depends on the metatheory below, so
-- both are checked here, before it.
open import strong-rep-var.TypeCheck
open import strong-rep-var.Eval

-- the main theorems
open import strong-rep-var.Preservation

-- progress (the canonical-forms suite, the proof script, the theorem)
open import strong-rep-var.Progress
open import strong-rep-var.TypeSafety

-- THE LIVING REGRESSION AND THE RENDERER (ported 2026-09-19, closing the
-- frontier).  `strong-rep-var.Examples` is closed programs, their runs, their
-- typings and the refutations that still hold, stated through
-- `TypeCheck.agda`/`Eval.agda` rather than by hand-written boundary
-- derivations; `strong-rep-var.Show` renders de Bruijn terms with names,
-- printing
-- the two universes differently (X names α) and a whole run with the rule
-- that fired at each step.
open import strong-rep-var.Examples

-- COLOR PRESERVATION (2026-09-21): the one-hole-context/residual layer
-- and the theorem STATEMENT.  The proof follows Jeremy's review of the
-- statement (notes/TODO.md).
open import strong-rep-var.Residual
open import strong-rep-var.ColorPreservation

-- Soundness of the residual layer: a residual names a position in the
-- contractum (`residual-sound`, `residuals-sound`).  Direct gate: no
-- top-level module reaches it until the theorem is proved.
open import strong-rep-var.proof.Residual
open import strong-rep-var.Show

-- THE SOUNDNESS GATE.  A conceal must cite a REPRESENTED binder, and the
-- two-universe design refuses it twice over: the name may be absent from
-- the map, or the representation variable it names may be `abstR`.
-- Direct gate: no top-level module reaches this soundness audit.
open import strong-rep-var.proof.Adversary

-- THE ID-LAYER FACTS.  What makes IdPush and CancelR legitimate: the
-- pushed name is already written in the inner conversion (one universe
-- up, on the representation variable), `unseal` is the only active
-- conversion an id-layer can meet, and the naked drop is unsound except
-- at an empty frame.
-- Direct gate: no top-level module reaches this id-layer audit.
open import strong-rep-var.proof.IdLayer

-- CANONICITY.  Every conversion reduction writes is in the canonical
-- family, and the family survives reduction — including `Peel`'s
-- re-spelling onto the dual's name map, which is what the two universes
-- added.
-- Direct gate: no top-level module reaches this canonicity audit.
open import strong-rep-var.proof.Canonicity

-- THE SHIFT AUDIT (2026-09-08, ported 2026-09-19).  Every rule that MOVES
-- a subterm, checked against frame exactness — now the relational
-- transport lemmas of strong-rep-var.Boundary §3a plus the observation that
-- every
-- move but TyBeta's is REPRESENTATION-ONLY — together with the tower
-- measure that makes the wrapper clause of TyPeelR terminate.
-- Direct gate: no top-level module reaches this shift audit.
open import strong-rep-var.proof.ShiftAudit

-- The checked notes come last because CancelRShiftWall reaches MoveScope.
open import strong-rep-var.notes.All
