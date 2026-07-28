module proof.Catchup.Core.NuImprecisionCatchupPrefixCloseLemma where

-- File Charter:
--   * Exposes the canonical live left-silent quotient-closing capability.
--   * Keeps callers independent of the close-frame implementation.
--   * Contains no semantic dispatcher, postulate, hole, permissive option, or
--     compatibility wrapper.

open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseDef
  using (LeftSilentIndexedPrefixCloseᵀ)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseProof
  using (left-silent-indexed-prefix-close-proofᵀ)


left-silent-indexed-prefix-closeᵀ :
  LeftSilentIndexedPrefixCloseᵀ
left-silent-indexed-prefix-closeᵀ =
  left-silent-indexed-prefix-close-proofᵀ
