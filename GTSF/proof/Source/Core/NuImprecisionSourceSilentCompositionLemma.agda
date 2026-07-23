module proof.Source.Core.NuImprecisionSourceSilentCompositionLemma where

-- File Charter:
--   * Exposes the canonical source-silent composition capability.
--   * Keeps canonical assembly separate from the frozen statement and proof.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.Source.Core.NuImprecisionSourceSilentCompositionDef using
  (SourceSilentComposition)
open import proof.Source.Core.NuImprecisionSourceSilentCompositionProof using
  (source-silent-composition-proofᵀ)


source-silent-compositionᵀ : SourceSilentComposition
source-silent-compositionᵀ = source-silent-composition-proofᵀ
