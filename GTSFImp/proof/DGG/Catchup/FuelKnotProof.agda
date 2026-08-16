module proof.DGG.Catchup.FuelKnotProof where

-- File Charter:
--   * LG-3 parked implementation site for the M6 fuel knot.
--   * The live knot records in `ValueCatchupRightDef` now use
--     inversion-based `ExtraCastRightAt` and `ValueCatchupRightAt`
--     surfaces with no provenance columns.
--   * Rebuilding the executable `Acc _<_` knot is blocked until the parked
--     extra-cast and column-recursion proofs are restored; see
--     `notes/lg3-extra-cast-right-blocked.red` and
--     `notes/lg3-value-catchup-column-blocked.red`.
