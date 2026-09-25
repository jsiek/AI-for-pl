module strong-rep-nu.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

-- the core
open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.Source
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Compile
open import strong-rep-nu.CompileTyping
open import strong-rep-nu.proof.Compile

-- executable, derivation-producing type checking, and the step function
-- that searches for a redex.  Neither depends on the metatheory below, so
-- both are checked here, before it.
open import strong-rep-nu.TypeCheck
open import strong-rep-nu.Eval

-- the main theorems; composition's typing (`⊢⨟`) is reached through
-- the Merge case of preservation
open import strong-rep-nu.proof.Compose
open import strong-rep-nu.Preservation

-- progress (the canonical-forms suite, the proof script, the theorem)
open import strong-rep-nu.Progress
open import strong-rep-nu.TypeSafety

-- THE LIVING REGRESSION AND THE RENDERER (ported 2026-09-19, closing the
-- frontier).  `strong-rep-nu.Examples` is closed programs, their runs, their
-- typings and the refutations that still hold, stated through
-- `TypeCheck.agda`/`Eval.agda` rather than by hand-written boundary
-- derivations; `strong-rep-nu.Show` renders de Bruijn terms with names,
-- printing
-- the two universes differently (X names α) and a whole run with the rule
-- that fired at each step.
open import strong-rep-nu.Examples
open import strong-rep-nu.SourceExamples

-- COLOR PRESERVATION (2026-09-21): the one-hole-context/residual layer,
-- the theorem, and its proof (reached through the public module).
open import strong-rep-nu.Residual
open import strong-rep-nu.ColorPreservation

-- Soundness of the residual layer: a residual names a position in the
-- contractum (`residual-sound`, `residuals-sound`).  Direct gate: the
-- theorem does not depend on it.
open import strong-rep-nu.proof.Residual
open import strong-rep-nu.Show

-- THE SOUNDNESS GATE.  A conceal must cite a REPRESENTED binder, and the
-- two-universe design refuses it twice over: the name may be absent from
-- the map, or the representation variable it names may be `abstR`.
-- Direct gate: no top-level module reaches this soundness audit.
open import strong-rep-nu.proof.Adversary

-- `_⊢_~_` IS RENAMING through the name map, on well-formed types.
-- Direct gate: nothing depends on this characterization.
open import strong-rep-nu.proof.SameRenaming

-- THE ID-LAYER FACTS about the `Merge` redexes the retired IdPush and
-- CancelR handled: the two names already denote one representation
-- variable, `unseal` is the only active conversion an id-layer can
-- meet, and the naked drop is unsound except at an empty frame.
-- Direct gate: no top-level module reaches this id-layer audit.
open import strong-rep-nu.proof.IdLayer

-- THE SHIFT AUDIT (2026-09-08, ported 2026-09-19).  Every rule that MOVES
-- a subterm, checked against frame exactness — now the relational
-- transport lemmas of strong-rep-nu.Boundary §3a plus the observation that
-- every move but the ν rules' refinement is REPRESENTATION-ONLY —
-- together with the tower measure: one boundary per value, and `Merge`
-- lowers it.
-- Direct gate: no top-level module reaches this shift audit.
open import strong-rep-nu.proof.ShiftAudit

-- The checked notes come last.
open import strong-rep-nu.notes.All
