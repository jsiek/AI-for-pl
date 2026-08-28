{-# OPTIONS --safe #-}

module proof.DGG.notes.ContextualSimClosingBoundaryProbe where

-- File Charter:
--   * Records the boundary mismatch found while starting the ContextualSim
--     proof skeleton and points to its promoted canonical definition.
--   * Pins the trusted non-top selected target reveal/source-rebase edge after
--     aligned allocation against that live constructor-form definition.
--
-- The existing ContextualTargetRevealRebaseClosingᵀ starts at the selected
-- reveal: its root target is the selected child wrapped by that reveal.  A
-- ContextualSim caller may have application, primitive, cast, or conversion
-- frames above the selected reveal.  Passing only the old inner path therefore
-- loses the caller target and source reconstruction.  The canonical context
-- definition now carries that selected edge explicitly and keeps the caller
-- world separate from the selected edge's world.  This probe retains only the
-- trusted non-top aligned-allocation pin for the promoted definition.

import Imprecision as I
import proof.DGG.Examples.TargetIdentityReveal as TIR
import proof.DGG.notes.ContextualSimPromotionProbe as CSP
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( TargetRevealRebaseInPath; selected-here; selected-there )
open import proof.DGG.SourceRebase using (source-rebase-now)


------------------------------------------------------------------------
-- Trusted non-top selection after aligned allocation
------------------------------------------------------------------------

tir-selected-inner-rebase :
  TargetRevealRebaseInPath
    TIR.checkpoint₁-beta-reveal⊢
    (source-rebase-now TIR.checkpoint₃-beta-ok
      TIR.checkpoint₃-beta-representation)
    TIR.checkpoint₃-function-imprecision
    (I.⇒⊑⇒ I.X⊑X I.★⊑★)
    CSP.tir-after-allocation-path
tir-selected-inner-rebase = selected-there selected-here
