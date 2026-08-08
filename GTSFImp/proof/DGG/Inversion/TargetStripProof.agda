module proof.DGG.Inversion.TargetStripProof where

-- File Charter:
--   * Provides the sliced target-tag-at-star strip members used by source
--     stripping.
--   * Keeps any remaining proof debt aligned with the validated target-seal
--     and target-tag slice surfaces.
--   * Derives the old compound strip inhabitants from those slices.

open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)

postulate
  seal-descent-at-var : SealDescentAtVar
  seal-descent-at-varᴸ : SealDescentAtVarᴸ
  tag-dispatch-at★ : TagDispatchAt★
  tag-dispatch-at★ᴸ : TagDispatchAt★ᴸ

target-strip-at★ : TargetStripAt★
target-strip-at★ =
  target-strip★-from-slices seal-descent-at-var tag-dispatch-at★

target-strip-at★ᴸ : TargetStripAt★ᴸ
target-strip-at★ᴸ =
  target-strip★ᴸ-from-slices seal-descent-at-varᴸ tag-dispatch-at★ᴸ
