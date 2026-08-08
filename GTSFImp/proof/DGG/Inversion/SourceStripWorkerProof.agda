module proof.DGG.Inversion.SourceStripWorkerProof where

-- File Charter:
--   * Isolates the remaining source-column and source-spine strip members.
--   * Keeps the public `SourceStripProof` module free of local postulates.
--   * The two statements are exactly the frozen worker goals from
--     `SourceStripDef`.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip)

postulate
  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker : SourceSpineStrip
