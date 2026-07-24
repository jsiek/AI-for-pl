module
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleLemma
  where

-- File Charter:
--   * Exposes the canonical contradiction for an atomic renamed target of
--     `Λ⊑instβᵀ`.
--   * Keeps atomic target reindexing independent of the shape proof.
--   * Contains no term relation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleDef
  using (LambdaInstBetaFinalTargetAtomicImpossibleᵀ)
open import
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleProof
  using
  (lambda-inst-beta-final-target-atomic-impossible-proofᵀ)


lambda-inst-beta-final-target-atomic-impossibleᵀ :
  LambdaInstBetaFinalTargetAtomicImpossibleᵀ
lambda-inst-beta-final-target-atomic-impossibleᵀ =
  lambda-inst-beta-final-target-atomic-impossible-proofᵀ
