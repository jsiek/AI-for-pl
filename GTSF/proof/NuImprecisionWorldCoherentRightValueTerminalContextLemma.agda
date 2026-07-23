module
  proof.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual zero-step seed for right-value
--     catch-up.
--   * Keeps callers independent of the ordinary terminal construction.
--   * Contains no result/view/outcome hierarchy, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import
  proof.NuImprecisionWorldCoherentRightValueTerminalContextDef
  using (WorldCoherentRightValueTerminalContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueTerminalContextProof
  using (world-coherent-right-value-terminal-context-proofᵀ)


world-coherent-right-value-terminal-contextᵀ :
  WorldCoherentRightValueTerminalContextᵀ
world-coherent-right-value-terminal-contextᵀ =
  world-coherent-right-value-terminal-context-proofᵀ
