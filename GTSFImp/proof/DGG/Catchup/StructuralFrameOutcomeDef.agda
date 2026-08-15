module proof.DGG.Catchup.StructuralFrameOutcomeDef where

-- File Charter:
--   * Classifies a value-administration term as a value or one keep step
--     from a value.

open import CastTerms using (Term; Value)
open import Reduction using (keep; _—→[_]_)


data StructuralFrameOutcome {Δ} (M : Term Δ) : Set where
  structural-frame-value :
    Value M
    → StructuralFrameOutcome M

  structural-frame-keep : ∀ {N}
    → M —→[ keep ] N
    → Value N
    → StructuralFrameOutcome M
