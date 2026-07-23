module
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalProof
  where

-- File Charter:
--   * Eliminates the final source-only `ν` terminal case with the fresh-path
--     cycle impossibility for the external paired universal conversion.
--   * Contains no cycle implementation, postulate, hole, permissive option,
--     continuation interpreter, semantic handler, or canonical assembly.

open import Data.Empty using (⊥-elim)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalDef
  using (PairedLambdaTargetClosingNuTerminalᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)


paired-lambda-target-closing-ν-terminal-proofᵀ :
  PairedUniversalConversionFreshPathCycleᵀ →
  PairedLambdaTargetClosingNuTerminalᵀ
paired-lambda-target-closing-ν-terminal-proofᵀ cycle
    vW noW vW′ noW′ W⊑W′ prefix coherent exclusive wfL h⇑A
    reveal liftν lift∀ conversion =
  ⊥-elim (cycle _ conversion)
