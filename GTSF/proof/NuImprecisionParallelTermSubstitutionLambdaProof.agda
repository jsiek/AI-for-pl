module proof.NuImprecisionParallelTermSubstitutionLambdaProof where

-- File Charter:
--   * Proves the ordinary-lambda parallel-substitution root from the framed
--     recursive capability.
--   * Extends the current frame once and reconstructs `ƛ⊑ƛᵀ`.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import QuotientedTermImprecision using (ƛ⊑ƛᵀ)
open import proof.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionFramedᵀ)
open import
  proof.NuImprecisionParallelTermSubstitutionLambdaDef
  using (QuotientedParallelTermSubstitutionLambdaᵀ)
open import proof.NuImprecisionSubstitutionFrame using
  (substitution-frame-ƛ)


quotiented-parallel-term-substitution-lambda-proofᵀ :
  QuotientedParallelTermSubstitutionFramedᵀ →
  QuotientedParallelTermSubstitutionLambdaᵀ
quotiented-parallel-term-substitution-lambda-proofᵀ
    parallel environment frame prefix noN noN′ hA hA′ body =
  ƛ⊑ƛᵀ hA hA′
    (parallel environment (substitution-frame-ƛ frame)
      prefix noN noN′ body)
