module proof.NuImprecisionTermSubstitutionProof where

-- File Charter:
--   * Derives single term substitution from prefix-aware parallel
--     substitution.
--   * Consumes the complete single-substitution binder environment instead of
--     assuming proof irrelevance for lifted precision indices.
--   * Contains no binder recursion, postulate, hole, catch-all, or permissive
--     option.

open import proof.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionᵀ)
open import proof.NuImprecisionSingleSubstitutionEnvironmentDef using
  (QuotientedSingleSubstitutionEnvironmentᵀ)
open import proof.NuImprecisionTermSubstitutionDef using
  (QuotientedTermSubstitutionᵀ)


quotiented-term-substitution-proofᵀ :
  QuotientedParallelTermSubstitutionᵀ →
  QuotientedSingleSubstitutionEnvironmentᵀ →
  QuotientedTermSubstitutionᵀ
quotiented-term-substitution-proofᵀ
    parallel single-environment unique noN noN′ noV noV′
    body argument =
  parallel (single-environment unique noV noV′ argument)
    noN noN′ body
