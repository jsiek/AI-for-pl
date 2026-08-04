module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareLemma
  where

-- File Charter:
--   * Canonically assembles both structural fresh-path target half-squares
--     from the strict imprecision arrow-route transport proofs.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, handler import, or broad simulation import.

open import
  proof.Source.FreshTypePath.NuImprecisionFreshTypePathImprecisionTransportProof
  using
  (fresh-type-path-imprecision-transport-proof)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareProof
  using
  ( paired-universal-conversion-fresh-path-target-structural-conceal-half-square-proofᵀ
  ; paired-universal-conversion-fresh-path-target-structural-reveal-half-square-proofᵀ
  )


paired-universal-conversion-fresh-path-target-structural-reveal-half-square-lemmaᵀ :
  PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-structural-reveal-half-square-lemmaᵀ
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at =
  paired-universal-conversion-fresh-path-target-structural-reveal-half-square-proofᵀ
    fresh-type-path-imprecision-transport-proof
    {r = r} {s = s}
    correspondence conversion occurs-B b-at e-at


paired-universal-conversion-fresh-path-target-structural-conceal-half-square-lemmaᵀ :
  PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-structural-conceal-half-square-lemmaᵀ
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at =
  paired-universal-conversion-fresh-path-target-structural-conceal-half-square-proofᵀ
    fresh-type-path-imprecision-transport-proof
    {r = r} {s = s}
    correspondence conversion occurs-B b-at e-at
