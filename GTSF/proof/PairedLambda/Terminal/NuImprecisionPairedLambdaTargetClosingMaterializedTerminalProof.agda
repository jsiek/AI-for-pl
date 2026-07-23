module
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingMaterializedTerminalProof
  where

-- File Charter:
--   * Dispatches materialized paired-lambda terminal closing on the final
--     source-only `ν` or paired-universal `∀ⁱ` imprecision index.
--   * Keeps both terminal cases as explicit higher-order dependencies.
--   * Contains no terminal implementation, postulate, hole, permissive
--     option, continuation interpreter, semantic handler, or canonical
--     assembly.

open import ImprecisionWf using (∀ⁱ_; ν)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingAllTerminalDef
  using (PairedLambdaTargetClosingAllTerminalᵀ)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingMaterializedTerminalDef
  using (PairedLambdaTargetClosingMaterializedTerminalᵀ)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalDef
  using (PairedLambdaTargetClosingNuTerminalᵀ)


paired-lambda-target-closing-materialized-terminal-proofᵀ :
  PairedLambdaTargetClosingNuTerminalᵀ →
  PairedLambdaTargetClosingAllTerminalᵀ →
  PairedLambdaTargetClosingMaterializedTerminalᵀ
paired-lambda-target-closing-materialized-terminal-proofᵀ
    close-ν close-∀ {q = ν _ occ r} vW noW vW′ noW′ W⊑W′ =
  close-ν vW noW vW′ noW′ W⊑W′
paired-lambda-target-closing-materialized-terminal-proofᵀ
    close-ν close-∀ {q = ∀ⁱ r} vW noW vW′ noW′ W⊑W′ =
  close-∀ vW noW vW′ noW′ W⊑W′
