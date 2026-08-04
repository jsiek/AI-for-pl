module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleLemma
  where

-- File Charter:
--   * Canonically assembles the fresh-path-cycle impossibility from the
--     strict fresh-path square lemma.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, handler import, or broad simulation import.

open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleProof
  using (paired-universal-conversion-fresh-path-cycle-proofᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathSquareLemma
  using (paired-universal-conversion-fresh-path-square-lemmaᵀ)


paired-universal-conversion-fresh-path-cycle-lemmaᵀ :
  PairedUniversalConversionFreshPathCycleᵀ
paired-universal-conversion-fresh-path-cycle-lemmaᵀ
    {r = r} {s = s} occurs-B conversion =
  paired-universal-conversion-fresh-path-cycle-proofᵀ
    paired-universal-conversion-fresh-path-square-lemmaᵀ
    {r = r} {s = s} occurs-B conversion
