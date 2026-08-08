module proof.DGG.Inversion.SourceStripLemma where

-- File Charter:
--   * Exposes the source-strip inhabitants at the Def types.
--   * Keeps consumers independent of the proof-script module name.
--   * Re-exports no target-walk or right-injection theorem.

open import proof.DGG.Inversion.SourceStripProof public using
  (source-column-strip; source-spine-strip; source-tag-seal-core)
