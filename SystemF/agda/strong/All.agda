module strong.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.
--
-- V8 MECHANIZATION IN PROGRESS (see notes/notes-v8.md).  The modules
-- below are commented out and return one by one as they are updated to
-- v8; `CtxMorph`, `ScopeDual`, and `AnchorWeaken` are deleted by the
-- design (no scopes in terms, no address shifting).

-- the core
open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
-- open import strong.TypeSubst
-- open import strong.Terms
-- open import strong.TermSubst
-- open import strong.Reduction
-- open import strong.Residual

-- the main theorems
-- open import strong.Preservation
-- open import strong.TypeSafety
-- open import strong.ColorPreservation
-- open import strong.Progress

-- the proof scripts
-- open import strong.proof.…   (returning with their subjects)

-- the regression corpus and the renderer
-- open import strong.Examples
-- open import strong.Show
-- open import strong.Eval
