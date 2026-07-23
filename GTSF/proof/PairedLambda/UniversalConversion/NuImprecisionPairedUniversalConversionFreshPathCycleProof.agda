module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleProof
  where

-- File Charter:
--   * Reduces the fresh-path-cycle impossibility to one joint path transport
--     around the imprecision/paired-conversion square.
--   * Converts boolean occurrence to a proof-relevant path and closes the
--     cycle with the finite self-extension contradiction.
--   * Keeps the missing joint transport as one named theorem parameter;
--     contains no postulate, hole, permissive option, or broad simulation
--     import.

open import Data.Product using (_,_)
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  ( occurs-to-var-at-path
  ; var-at-path-not-below-itself
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathSquareDef
  using (PairedUniversalConversionFreshPathSquareᵀ)


paired-universal-conversion-fresh-path-cycle-proofᵀ :
  PairedUniversalConversionFreshPathSquareᵀ →
  PairedUniversalConversionFreshPathCycleᵀ
paired-universal-conversion-fresh-path-cycle-proofᵀ
    transport occ-r conversion
    with occurs-to-var-at-path occ-r
paired-universal-conversion-fresh-path-cycle-proofᵀ
    transport occ-r conversion | p , x-at =
  var-at-path-not-below-itself x-at
    (transport x-at occ-r conversion)
