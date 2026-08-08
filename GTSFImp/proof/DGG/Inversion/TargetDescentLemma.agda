module proof.DGG.Inversion.TargetDescentLemma where

-- File Charter:
--   * Exposes the checked target-star descent helpers used by M3 inversion.
--   * Keeps consumers independent of the proof script module names.
--   * Re-exports no OpenStrata or SealChain machinery.

open import proof.DGG.Inversion.TargetDescentProof public using
  (composeSamePivotRebase; inner-source-pivot-eqᴿ;
   target-seal★-descent; target-seal★-extract;
   target-seal＇-reemit)
