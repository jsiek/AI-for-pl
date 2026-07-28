module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedProof
  where

-- File Charter:
--   * Assembles the four exact paired function-cast beta terminals.
--   * Keeps ordinary paired reveal, conceal, and widening proofs separate
--     from quotient closure.
--   * Contains no semantic implementation, recursion, retired paired-cast
--     carrier, postulate, hole, permissive option, or wrapper.

open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedConversionProof
  using
  ( right-step-application-function-cast-beta-paired-conceal-values-proofᵀ
  ; right-step-application-function-cast-beta-paired-reveal-values-proofᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  using
  (WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientProof
  using
  (right-step-application-function-cast-beta-paired-quotient-values-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedWideningProof
  using
  (right-step-application-function-cast-beta-paired-widening-values-proofᵀ)


world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ →
  SourceFunctionCastBetaPairedQuotientRelationᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues
world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ
    function-compatible quotient =
  record
    { rightStepApplicationFunctionCastBetaPairedRevealValues =
        right-step-application-function-cast-beta-paired-reveal-values-proofᵀ
    ; rightStepApplicationFunctionCastBetaPairedConcealValues =
        right-step-application-function-cast-beta-paired-conceal-values-proofᵀ
    ; rightStepApplicationFunctionCastBetaPairedWideningValues =
        right-step-application-function-cast-beta-paired-widening-values-proofᵀ
          function-compatible
    ; rightStepApplicationFunctionCastBetaPairedQuotientValues =
        right-step-application-function-cast-beta-paired-quotient-values-proofᵀ
          quotient
    }
