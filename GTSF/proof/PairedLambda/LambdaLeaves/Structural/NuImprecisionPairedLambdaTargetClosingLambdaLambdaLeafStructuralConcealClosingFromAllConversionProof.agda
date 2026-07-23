module
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingFromAllConversionProof
  where

-- File Charter:
--   * Reduces the matched-`Lambda` structural conceal leaf to the shared fused
--     source-`nu`/paired-universal closing theorem.
--   * Reconstructs the outer matched-lambda relation, transports it through
--     the ambient prefix, and packages the nested source conceal and target
--     body conceal as one paired universal conversion.
--   * Records statement fit only; the dependency is equivalent to the larger
--     recursive root and therefore is not the canonical proof direction.
--   * Contains no canonical assembly, postulate, hole, permissive option,
--     broad simulation import, or pre-final-reveal intermediate index.

open import Data.Nat.Properties using (≤-refl)
open import Conversion using (conceal-all)
open import NuTerms using (Λ_; no•-Λ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-conceal
  ; Λ⊑Λᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import proof.Core.Properties.TypePreservation using (term-weaken)


paired-lambda-target-closing-lambda-lambda-leaf-structural-conceal-closing-from-all-conversion-proofᵀ :
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-structural-conceal-closing-from-all-conversion-proofᵀ
    closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    corresponds
    source-conceal target-conceal =
  closing {q = q} coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    lambda-value lambda-no-bullet
    lambda-value′ lambda-no-bullet′
    (paired-conceal corresponds
      (conceal-all (conceal-all source-conceal))
      (conceal-all target-conceal))
    lambda-relation
  where
  lambda-value = Λ vV

  lambda-no-bullet = no•-Λ noV

  lambda-value′ = Λ vV′

  lambda-no-bullet′ = no•-Λ noV′

  lambda-relation₀ = Λ⊑Λᵀ liftΛ liftγ vV vV′ V⊑V′

  lambda-relation =
    allocation-prefixᵀ prefix lambda-relation₀
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        lambda-no-bullet
        (nu-term-imprecision-source-typing lambda-relation₀))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        lambda-no-bullet′
        (nu-term-imprecision-target-typing lambda-relation₀))
