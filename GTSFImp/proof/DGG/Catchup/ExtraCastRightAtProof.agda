module proof.DGG.Catchup.ExtraCastRightAtProof where

-- File Charter:
--   * LG-3 parked implementation site for the fuel-indexed
--     `ExtraCastRightAt` proof.
--   * The live fuel surface in `ValueCatchupRightDef` now consumes the
--     casted-target CTI premise directly.
--   * The old proof was deleted with the cast-provenance family.  Rebuilding
--     it is blocked on the same target-cast CTI inversion surface as the
--     non-fuel proof; see `notes/lg3-extra-cast-right-blocked.red`.
