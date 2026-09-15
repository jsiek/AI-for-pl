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
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.Examples

-- the proof scripts
open import strong.proof.Interior
open import strong.proof.Canonical
open import strong.proof.Progress
open import strong.proof.ConvCanonicity
open import strong.proof.CompositionTyping
open import strong.proof.PreserveMerge
open import strong.proof.PreserveConst
open import strong.proof.ArrTyping
open import strong.proof.InertRenaming
open import strong.proof.Flat
open import strong.proof.StoreWeaken
open import strong.proof.PreserveWrap
open import strong.proof.AddrWeaken
open import strong.proof.TermSubstitution
open import strong.proof.AllTyping
open import strong.proof.SrcTyping
open import strong.proof.PreserveTyDef
open import strong.proof.Preservation

-- the main theorems
open import strong.Progress
-- open import strong.TypeSubst
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
