module proof.DGG.Inversion.SourceStripWorkerProof where

-- File Charter:
--   * Provides the source-column and source-spine strip members.
--   * Keeps the public `SourceStripProof` module free of local proof scripts.
--   * The two statements are exactly the frozen worker goals from
--     `SourceStripDef`.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip)

-- The worker statements are still being recut.  The checked obstruction is
-- that the old column worker asked for inverse rebase transport with no
-- enclosing source wrapper.  Keep the module green while the public strip
-- surface and consumers are adjusted around the restricted branch data.
postulate
  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker : SourceSpineStrip
