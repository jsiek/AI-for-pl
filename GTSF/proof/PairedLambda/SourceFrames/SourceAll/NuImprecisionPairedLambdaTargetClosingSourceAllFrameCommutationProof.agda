module
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationProof
  where

-- File Charter:
--   * Proves source-universal-frame commutation by an exhaustive split on the
--     framed relation's outer precision index.
--   * Delegates the genuinely fused structural-all branch, while the
--     source-only `ν` branch rotates the paired conversion, allocates the
--     source runtime bullet, and applies the final reveal directly.
--   * Uses no source-only intermediate index in the structural-all branch.
--   * Contains no canonical assembly, postulate, hole, permissive option, or
--     broad simulation/core import.

import Coercions as C
open import Conversion using (reveal-all)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using (ν; ∀ⁱ_)
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-conversion
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using
  (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationDef
  using (PairedLambdaTargetClosingSourceAllFrameCommutationᵀ)
open import proof.Source.Core.NuImprecisionSourceBulletBase using
  (left-allocated-bulletᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import proof.Core.Properties.TypePreservation using (term-weaken)


paired-lambda-target-closing-source-all-frame-commutation-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ →
  PairedLambdaTargetClosingSourceAllFrameCommutationᵀ
paired-lambda-target-closing-source-all-frame-commutation-proofᵀ
    rotate-conversion all-closing {r = ∀ⁱ r}
    vW noW vW′ noW′ relation framed inner =
  all-closing vW noW vW′ noW′ relation framed inner
paired-lambda-target-closing-source-all-frame-commutation-proofᵀ
    rotate-conversion all-closing {d = d} {r = ν _ occ-r r}
    vW noW vW′ noW′ relation framed inner
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
    with rotate-conversion h⇑A liftν occ-r conversion
paired-lambda-target-closing-source-all-frame-commutation-proofᵀ
    rotate-conversion all-closing {d = d} {r = ν _ occ-r r}
    vW noW vW′ noW′ relation framed inner
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
    | u , rotated-conversion =
  conv↑⊑ᵀ (reveal-all reveal)
    (conv⊑convᵀ (paired-conversion rotated-conversion)
      bullet-relation)
    (⊑-source-liftνᵢ _)
  where
  framed-value = vW ⟨ C.`∀ d ⟩

  framed-no-bullet = no•-⟨⟩ noW

  ambient-relation =
    allocation-prefixᵀ prefix framed
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        framed-no-bullet
        (nu-term-imprecision-source-typing framed))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noW′ (nu-term-imprecision-target-typing framed))

  bullet-relation =
    left-allocated-bulletᵀ framed-value framed-no-bullet
      h⇑A liftν ambient-relation
