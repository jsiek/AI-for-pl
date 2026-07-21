module proof.NuImprecisionCorrespondingSourceNameNotStarLemma where

-- File Charter:
--   * Canonically assembles the corresponding-source-name exclusion theorem.
--   * Keeps canonical assembly separate from the frozen statement and proof.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.NuImprecisionCorrespondingSourceNameNotStarDef using
  (CorrespondingSourceNameNotStarᵀ)
open import proof.NuImprecisionCorrespondingSourceNameNotStarProof using
  (corresponding-source-name-not-star-proofᵀ)


corresponding-source-name-not-starᵀ : CorrespondingSourceNameNotStarᵀ
corresponding-source-name-not-starᵀ =
  corresponding-source-name-not-star-proofᵀ
