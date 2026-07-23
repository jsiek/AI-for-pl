module proof.NuImprecisionRightSourceAllClosingTerminalLemma where

-- File Charter:
--   * Exposes the canonical value/value terminal base of world-coherent right
--     source-universal closing.
--   * Contains no implementation, recursion, compatibility wrapper,
--     postulate, hole, permissive option, or broad simulation import.

open import
  proof.NuImprecisionRightSourceAllClosingTerminalDef
  using (WorldCoherentRightSourceAllClosingTerminalᵀ)
open import
  proof.NuImprecisionRightSourceAllClosingTerminalProof
  using (world-coherent-right-source-all-closing-terminal-proofᵀ)


world-coherent-right-source-all-closing-terminalᵀ :
  WorldCoherentRightSourceAllClosingTerminalᵀ
world-coherent-right-source-all-closing-terminalᵀ =
  world-coherent-right-source-all-closing-terminal-proofᵀ
