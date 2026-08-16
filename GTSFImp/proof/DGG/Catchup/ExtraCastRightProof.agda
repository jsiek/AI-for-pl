module proof.DGG.Catchup.ExtraCastRightProof where

-- File Charter:
--   * LG-3 parked implementation site for the non-fuel `ExtraCastRight²`
--     proof.
--   * The live statement in `proof.DGG.ExtraCastRight2` now consumes the
--     whole CTI derivation for the casted target and carries no
--     separate cast-provenance premise.
--   * The old proof was deleted with the cast-provenance family.  Rebuilding
--     this theorem needs the blocked CTI target-cast preservation/inversion
--     surface recorded in `notes/lg3-extra-cast-right-blocked.red`.
