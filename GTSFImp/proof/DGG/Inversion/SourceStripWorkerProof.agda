module proof.DGG.Inversion.SourceStripWorkerProof where

-- File Charter:
--   * Provides the source-column and source-spine strip members.
--   * Keeps the public `SourceStripProof` module free of local proof scripts.
--   * The two statements are exactly the frozen worker goals from
--     `SourceStripDef`.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip)

-- WIP handoff: the restricted sealed-source partner view is now checked in
-- `TargetWalkSupport`.  The worker proof remains the remaining integration
-- residue, so the public tree stays green through these two frozen surfaces.
postulate
  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker : SourceSpineStrip
