module
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareProof
  where

-- File Charter:
--   * Proves the structural reveal and conceal target half-squares after a
--     paired-universal conversion is inverted.
--   * Sends the fresh paired-binder path forward through target imprecision,
--     backward through conversion, and contradicts the source-only path on
--     the same arrow route.
--   * Contains no dispatcher, postulate, hole, permissive option, handler
--     import, or broad simulation import.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import proof.EndpointCanonicalMLBSimpleFactor using
  (star-track-ν-zero; var-track-∀-zero)
open import proof.NuImprecisionFreshTypePath using (at-body)
open import proof.NuImprecisionFreshTypePathImprecisionTransportDef using
  ( FreshTypePathImprecisionTransport
  ; matched-source-path-forward
  ; source-only-to-universal-body-impossible
  )
open import proof.NuImprecisionFreshTypePathTransport using
  (conceal-fresh-path-backward; reveal-fresh-path-backward)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
  )


paired-universal-conversion-fresh-path-target-structural-reveal-half-square-proofᵀ :
  FreshTypePathImprecisionTransport →
  PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-structural-reveal-half-square-proofᵀ
    transport
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at
    with matched-source-path-forward
      transport var-track-∀-zero s (at-body e-at)
paired-universal-conversion-fresh-path-target-structural-reveal-half-square-proofᵀ
    transport
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at
    | q , route , c-at =
  ⊥-elim
    (source-only-to-universal-body-impossible
      transport star-track-ν-zero r b-at
      (reveal-fresh-path-backward conversion c-at) route)


paired-universal-conversion-fresh-path-target-structural-conceal-half-square-proofᵀ :
  FreshTypePathImprecisionTransport →
  PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-structural-conceal-half-square-proofᵀ
    transport
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at
    with matched-source-path-forward
      transport var-track-∀-zero s (at-body e-at)
paired-universal-conversion-fresh-path-target-structural-conceal-half-square-proofᵀ
    transport
    {r = r} {s = s} correspondence conversion occurs-B b-at e-at
    | q , route , c-at =
  ⊥-elim
    (source-only-to-universal-body-impossible
      transport star-track-ν-zero r b-at
      (conceal-fresh-path-backward conversion c-at) route)
