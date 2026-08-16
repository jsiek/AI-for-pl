module proof.DGG.Catchup.ExtraCastRightAtProof where

-- File Charter:
--   * LG-3 parked implementation site for the fuel-indexed
--     `ExtraCastRightAt` proof.
--   * The live fuel surface in `ValueCatchupRightDef` now consumes the
--     casted-target CTI premise directly.
--   * The internal worker surface carries `StructuralWorldExtendᴿ`; the
--     adapter in `StructuralCatchupRightDef` erases it to the public
--     `WorldExtendᴿ` boundary.

open import proof.DGG.Catchup.StructuralCatchupRightDef public using
  (StructuralCatchupRightResult; StructuralExtraCastRightAt;
   erase-structural-extra-cast-right-at)
