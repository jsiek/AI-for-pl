module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionLemma where

-- File Charter:
--   * Assembles public same-world parallel substitution from the structurally
--     recursive prefix-aware framed theorem.
--   * Instantiates the recursion at the identity binder frame.
--   * Contains no relation traversal, postulate, hole, or permissive option.

open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionᵀ)
open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionProof using
  (quotiented-parallel-term-substitution-framed-proofᵀ)
open import proof.Substitution.Term.NuImprecisionSubstitutionFrame using
  (substitution-frame-id)
open import QuotientedTermImprecision using (prefix-reflⁱ)


quotiented-parallel-term-substitution-lemmaᵀ :
  QuotientedParallelTermSubstitutionᵀ
quotiented-parallel-term-substitution-lemmaᵀ
    environment noN noN′ body =
  quotiented-parallel-term-substitution-framed-proofᵀ
    environment substitution-frame-id prefix-reflⁱ noN noN′ body
