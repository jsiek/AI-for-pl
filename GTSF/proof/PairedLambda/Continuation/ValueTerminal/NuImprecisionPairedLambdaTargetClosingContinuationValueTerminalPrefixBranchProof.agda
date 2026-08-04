module
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalPrefixBranchProof
  where

-- File Charter:
--   * Proves closure of the continuation-indexed paired-lambda terminal motive
--     under one relational-store allocation prefix.
--   * Takes the already-computed recursive continuation motive as an input and
--     prepends the pending prefix to the requested target continuation.
--   * Depends only on the branch statement and pending-target frame
--     constructor; contains no materialization, terminal, interpreter, handler,
--     frame-view, broad simulation, postulate, hole, or permissive option.

open import
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalPrefixBranchDef
  using (PairedLambdaTargetClosingContinuationValueTerminalPrefixBranchᵀ)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (pending-prefix)


paired-lambda-target-closing-continuation-value-terminal-prefix-branch-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalPrefixBranchᵀ
paired-lambda-target-closing-continuation-value-terminal-prefix-branch-proofᵀ
    closingᴷ prefix W⊢ W′⊢ pending =
  closingᴷ (pending-prefix prefix W⊢ W′⊢ pending)
