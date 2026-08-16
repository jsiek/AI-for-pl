module proof.DGG.Catchup.ValueCatchupRightProof where

-- File Charter:
--   * LG-3 parked implementation site for the fuel-indexed value catch-up
--     column recursion.
--   * `ValueCatchupRightAt` now consumes the CTI derivation for the whole
--     target term rather than a separate column witness.
--   * The internal worker surface carries `StructuralWorldExtendᴿ`; the
--     adapter in `StructuralCatchupRightDef` erases it to the public
--     `WorldExtendᴿ` boundary.

open import proof.DGG.Catchup.StructuralCatchupRightDef public using
  (StructuralCatchupRightResult; StructuralValueCatchupRightAt;
   erase-structural-value-catchup-right-at)
