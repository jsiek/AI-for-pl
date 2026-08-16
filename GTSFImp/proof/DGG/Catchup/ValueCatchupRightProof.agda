module proof.DGG.Catchup.ValueCatchupRightProof where

-- File Charter:
--   * LG-3 parked implementation site for the fuel-indexed value catch-up
--     column recursion.
--   * `ValueCatchupRightAt` now consumes the CTI derivation for the whole
--     target term rather than a separate column witness.
--   * Rebuilding the recursion needs a wrapper-aware target-cast-step
--     inversion theorem over CTI derivations; see
--     `notes/lg3-value-catchup-column-blocked.red`.
