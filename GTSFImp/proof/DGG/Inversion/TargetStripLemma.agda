module proof.DGG.Inversion.TargetStripLemma where

-- File Charter:
--   * Exposes the target-strip inhabitants at the Def types.
--   * Keeps consumers independent of the proof-script module name.
--   * Re-exports no source-strip or target-walk theorem.

open import proof.DGG.Inversion.TargetStripProof public using
  (target-strip-at★; target-strip-at★ᴸ)
