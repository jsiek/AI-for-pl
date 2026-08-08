module proof.DGG.Inversion.TargetStripProof where

-- File Charter:
--   * Provides the target-tag-at-star strip members used by source stripping.
--   * Keeps any remaining proof debt isolated from the source-strip
--     composition module.
--   * Exposes only inhabitants of the frozen `TargetStripDef` surfaces.

open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★; TargetStripAt★ᴸ)

postulate
  target-strip-at★ : TargetStripAt★
  target-strip-at★ᴸ : TargetStripAt★ᴸ
