module proof.DGG.Core.NuDGGTerminalSkeleton where

-- File Charter:
--   * Checks the end-to-end fit of the three named terminal proof boundaries.
--   * Contains no holes itself; the imported terminal proof modules remain
--     explicitly partial until their operational proofs are completed.

open import DynamicGradualGuarantee using (GradualDGG)
open import proof.DGG.Core.NuDGGTerminal using (terminal-components⇒gradual-dgg)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardBlame using
  (backward-target-blameᵀ)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueLemma using
  (backward-target-value-or-source-blameᵀ)
open import proof.DGG.TerminalForward.NuDGGTerminalForward using (forward-source-valueᵀ)


dynamic-gradual-guarantee-skeleton : GradualDGG
dynamic-gradual-guarantee-skeleton =
  terminal-components⇒gradual-dgg
    forward-source-valueᵀ
    backward-target-value-or-source-blameᵀ
    backward-target-blameᵀ
