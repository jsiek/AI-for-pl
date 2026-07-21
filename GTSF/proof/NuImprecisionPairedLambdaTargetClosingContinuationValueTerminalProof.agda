module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalProof
  where

-- File Charter:
--   * Proves common continuation-value terminal closing by materializing the
--     pending target continuation and invoking materialized terminal closing.
--   * Keeps both operations as explicit higher-order dependencies.
--   * Contains no terminal-core implementation, postulate, hole, permissive
--     option, semantic handler, frame view, or canonical assembly.

open import Data.Product using (_,_)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingMaterializedTerminalDef
  using (PairedLambdaTargetClosingMaterializedTerminalᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetMaterializationDef
  using (PairedLambdaTargetClosingPendingTargetMaterializationᵀ)


paired-lambda-target-closing-continuation-value-terminal-proofᵀ :
  PairedLambdaTargetClosingPendingTargetMaterializationᵀ →
  PairedLambdaTargetClosingMaterializedTerminalᵀ →
  PairedLambdaTargetClosingContinuationValueTerminalᵀ
paired-lambda-target-closing-continuation-value-terminal-proofᵀ
    materialize close vW noW vW′ noW′ W⊑W′ pending
    with materialize vW′ noW′ W⊑W′ pending
paired-lambda-target-closing-continuation-value-terminal-proofᵀ
    materialize close vW noW vW′ noW′ W⊑W′ pending
    | vW⁺ , noW⁺ , W⊑W⁺ = close vW noW vW⁺ noW⁺ W⊑W⁺
