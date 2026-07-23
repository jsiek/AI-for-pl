module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationProof
  where

-- File Charter:
--   * Proves the source-only `ν` paired-conversion rotation from the focused
--     fresh-path-cycle impossibility theorem.
--   * Makes explicit that the paired universal-conversion premise is
--     eliminated before any store allocation evidence is needed.
--   * Contains no path-cycle implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical assembly.

open import Data.Empty using (⊥-elim)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)


paired-lambda-target-closing-ν-paired-conversion-rotation-proofᵀ :
  PairedUniversalConversionFreshPathCycleᵀ →
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ
paired-lambda-target-closing-ν-paired-conversion-rotation-proofᵀ
    cycle h⇑Aν liftν occ-r conversion =
  ⊥-elim (cycle occ-r conversion)
