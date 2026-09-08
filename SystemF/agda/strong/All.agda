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

-- the main theorems
open import strong.Preservation
open import strong.TypeSafety

-- the proof scripts
open import strong.proof.Adversary
open import strong.proof.MaskFacts
open import strong.proof.IdLayer
open import strong.proof.Preserve
open import strong.proof.PeelDual
open import strong.proof.MoveScope
open import strong.proof.TypeSafety
open import strong.proof.PreserveObstruct

-- the TIGHTNESS OF THE DUAL: the defect (`Peel` gained scope), its
-- repair, and the frame choice the repair forced
open import strong.proof.DualTightness
open import strong.proof.MwUObstruct

-- NORMALISING THE CHANGE LISTS: the two redundancy tests that landed
-- (strong.CtxMorph §4) and the contractions that are REFUSED
open import strong.proof.RewindNorm

-- the regression corpus and the renderer
open import strong.Examples
open import strong.Show
open import strong.proof.Canonicity

-- progress (the canonical-forms suite, the proof script, the theorem)
open import strong.proof.Canonical
open import strong.proof.Progress
open import strong.Progress

-- the evaluator: `step` IS progress, `eval` iterates it under
-- preservation, and a Trace stores the step derivations it took
open import strong.Eval

-- THE WALL.  The search for an INVARIANT grounding the premise
-- `interior Θ₂ Δ ⊢ᵗ A` — the one the old CancelR/IdPush contracta needed —
-- is recorded in notes/DECISIONS.md (2026-09-06 entries).  The SCOPE MOVE
-- (strong.CtxMorph §4) removes the need, so the development carries no
-- module for it; the two surviving artifacts are proof/MaskFacts.mask-only
-- and Examples §12/§12b.
