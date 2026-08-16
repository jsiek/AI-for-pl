module proof.DGG.Catchup.ValueCatchupRightProof where

-- File Charter:
--   * LG-3 parked implementation site for the fuel-indexed value catch-up
--     column recursion.
--   * `ValueCatchupRightAt` now consumes the CTI derivation for the whole
--     syntactic cast column rather than a separate column witness.
--   * Rebuilding the recursion needs a column-layer CTI inversion theorem
--     that peels `applyColumn` one cast at a time; see
--     `notes/lg3-value-catchup-column-blocked.red`.
