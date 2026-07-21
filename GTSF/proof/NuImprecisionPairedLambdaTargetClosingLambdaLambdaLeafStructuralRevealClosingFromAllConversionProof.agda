module
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingFromAllConversionProof
  where

-- File Charter:
--   * Reduces the matched-`Lambda` structural reveal leaf to the shared fused
--     source-`nu`/paired-universal closing theorem.
--   * Reconstructs the outer matched-lambda relation, transports it through
--     the ambient prefix, and packages the two body reveals as one paired
--     universal conversion.
--   * Records statement fit only; the dependency is equivalent to the larger
--     recursive root and therefore is not the canonical proof direction.
--   * Contains no canonical assembly, postulate, hole, permissive option,
--     broad simulation import, or pre-final-reveal intermediate index.

open import Data.Nat.Properties using (≤-refl)
open import Conversion using (reveal-all)
open import NuTerms using (Λ_; no•-Λ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-reveal
  ; Λ⊑Λᵀ
  )
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import proof.TypePreservation using (term-weaken)


paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-from-all-conversion-proofᵀ :
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-from-all-conversion-proofᵀ
    closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix h⇑Aν final-reveal liftν lift∀ corresponds
    source-reveal target-reveal =
  closing {q = q} h⇑Aν final-reveal liftν lift∀
    lambda-value lambda-no-bullet
    lambda-value′ lambda-no-bullet′
    (paired-reveal corresponds
      (reveal-all source-reveal) (reveal-all target-reveal))
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
