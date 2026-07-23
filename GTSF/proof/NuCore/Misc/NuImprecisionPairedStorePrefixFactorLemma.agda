module proof.NuCore.Misc.NuImprecisionPairedStorePrefixFactorLemma where

-- File Charter:
--   * Exposes the canonical matched-store prefix-factorization lemma.
--   * Keeps the public inhabitant separate from its structural proof module.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.NuCore.Misc.NuImprecisionPairedStorePrefixFactorDef using
  (PairedStorePrefixFactorᵀ)
open import proof.NuCore.Misc.NuImprecisionPairedStorePrefixFactorProof using
  (paired-store-prefix-factor-proofᵀ)


paired-store-prefix-factorᵀ : PairedStorePrefixFactorᵀ
paired-store-prefix-factorᵀ = paired-store-prefix-factor-proofᵀ
