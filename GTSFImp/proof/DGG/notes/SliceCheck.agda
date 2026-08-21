module SliceCheck where

-- File Charter:
--   * Checks that the public target seal/tag slices still assemble at the
--     ordinary and left-lifted indices.
--   * Deliberately contains no source-fold or target-walk compatibility
--     surface; those overgeneralized consumers are retired.

open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)

------------------------------------------------------------------------
-- Validation A: sliced corollaries at the public recut indices
------------------------------------------------------------------------

target-strip★-from-slices-check :
  SealDescentAtVar
  → TagDispatchAt★
  → TargetStripAt★
target-strip★-from-slices-check =
  target-strip★-from-slices

target-strip★ᴸ-from-slices-check :
  SealDescentAtVarᴸ
  → TagDispatchAt★ᴸ
  → TargetStripAt★ᴸ
target-strip★ᴸ-from-slices-check =
  target-strip★ᴸ-from-slices
