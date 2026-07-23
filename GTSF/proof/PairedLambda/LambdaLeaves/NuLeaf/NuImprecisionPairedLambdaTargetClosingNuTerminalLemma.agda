module
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalLemma
  where

-- File Charter:
--   * Canonically assembles terminal paired-lambda closing for a source-only
--     `nu` index from the strict fresh-path-cycle lemma.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, continuation interpreter, or semantic handler.

open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalDef
  using (PairedLambdaTargetClosingNuTerminalᵀ)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalProof
  using (paired-lambda-target-closing-ν-terminal-proofᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleLemma
  using (paired-universal-conversion-fresh-path-cycle-lemmaᵀ)


paired-lambda-target-closing-ν-terminal-lemmaᵀ :
  PairedLambdaTargetClosingNuTerminalᵀ
paired-lambda-target-closing-ν-terminal-lemmaᵀ
    {r = r} vW noW vW′ noW′ W⊑W′ prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ conversion =
  paired-lambda-target-closing-ν-terminal-proofᵀ
    paired-universal-conversion-fresh-path-cycle-lemmaᵀ
    {r = r} vW noW vW′ noW′ W⊑W′ prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ conversion
