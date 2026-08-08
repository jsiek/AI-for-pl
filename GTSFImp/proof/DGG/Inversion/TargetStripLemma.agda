module proof.DGG.Inversion.TargetStripLemma where

-- File Charter:
--   * Exposes the target-strip inhabitants at the Def types.
--   * Keeps consumers independent of the proof-script module name.
--   * Re-exports no source-strip or target-walk theorem.

open import proof.DGG.Inversion.TargetStripProof public using
  (seal-descent-at-var; seal-descent-at-varᴸ; tag-dispatch-at★;
   tag-dispatch-at★ᴸ; target-strip-at★; target-strip-at★ᴸ)
