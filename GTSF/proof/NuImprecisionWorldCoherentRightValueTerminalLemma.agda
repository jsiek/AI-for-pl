module proof.NuImprecisionWorldCoherentRightValueTerminalLemma where

-- File Charter:
--   * Supplies the canonical right-value terminal base from its strict proof.
--   * Keeps recursive catch-up callers independent of the worker proof module.
--   * Contains no postulate, hole, permissive option, or broad simulation
--     import.

open import proof.NuImprecisionWorldCoherentRightValueTerminalDef using
  (WorldCoherentRightValueTerminalᵀ)
open import proof.NuImprecisionWorldCoherentRightValueTerminalProof using
  (world-coherent-right-value-terminal-proofᵀ)


world-coherent-right-value-terminalᵀ :
  WorldCoherentRightValueTerminalᵀ
world-coherent-right-value-terminalᵀ =
  world-coherent-right-value-terminal-proofᵀ
