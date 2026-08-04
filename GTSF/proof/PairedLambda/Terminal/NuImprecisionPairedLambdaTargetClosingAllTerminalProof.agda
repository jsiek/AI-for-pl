module
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingAllTerminalProof
  where

-- File Charter:
--   * Derives paired-universal terminal closing from direct continuation-value
--     terminal closing by choosing the empty pending continuation.
--   * Records the intended non-circular dependency direction: all-terminal
--     closing is a corollary, while continuation-value terminal closing is the
--     direct recursive semantic root.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, materialization dependency, semantic handler, or canonical
--     assembly.

open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingAllTerminalDef
  using (PairedLambdaTargetClosingAllTerminalᵀ)
open import
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (pending-refl)


paired-lambda-target-closing-all-terminal-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  PairedLambdaTargetClosingAllTerminalᵀ
paired-lambda-target-closing-all-terminal-proofᵀ
    close vW noW vW′ noW′ W⊑W′ =
  close vW noW vW′ noW′ W⊑W′ pending-refl
