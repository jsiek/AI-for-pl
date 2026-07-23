module proof.NuCore.Relations.NuImprecisionMatchedLiftInvariantsLemma where

-- File Charter:
--   * Exposes the canonical matched-lift invariant-preservation theorem.
--   * Keeps canonical assembly separate from the frozen statement and proof.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.NuCore.Relations.NuImprecisionMatchedLiftInvariantsDef using
  (MatchedLiftInvariantsᵀ)
open import proof.NuCore.Relations.NuImprecisionMatchedLiftInvariantsProof using
  (matched-lift-invariants-proofᵀ)


matched-lift-invariantsᵀ : MatchedLiftInvariantsᵀ
matched-lift-invariantsᵀ = matched-lift-invariants-proofᵀ
