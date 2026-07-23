module proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingTerminalProof where

-- File Charter:
--   * Proves the value/value terminal base of right source-universal closing.
--   * Reconstructs the outer `Λ⊑ᵀ` relation and delegates only the
--     canonical zero-step world-coherent terminal packaging.
--   * Contains no recursion, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import NuTerms using (Λ_; no•-Λ)
open import QuotientedTermImprecision using (Λ⊑ᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingTerminalDef
  using (WorldCoherentRightSourceAllClosingTerminalᵀ)
open import proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalLemma using
  (world-coherent-right-value-terminalᵀ)


world-coherent-right-source-all-closing-terminal-proofᵀ :
  WorldCoherentRightSourceAllClosingTerminalᵀ
world-coherent-right-source-all-closing-terminal-proofᵀ
    prefix coherent exclusive unique wfR
    vV noV vV′ noV′ liftρ liftγ body =
  world-coherent-right-value-terminalᵀ
    prefix coherent exclusive unique wfR
    (Λ vV) (no•-Λ noV) vV′ noV′
    (Λ⊑ᵀ _ liftρ liftγ vV body)
