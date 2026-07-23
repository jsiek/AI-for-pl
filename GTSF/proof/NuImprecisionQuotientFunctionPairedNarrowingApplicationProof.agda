module
  proof.NuImprecisionQuotientFunctionPairedNarrowingApplicationProof
  where

-- File Charter:
--   * Proves quotient-function paired-narrowing application introduction.
--   * Uses the application-specific core quotient constructor.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import
  proof.NuImprecisionQuotientFunctionPairedNarrowingApplicationDef
  using (QuotientFunctionPairedNarrowingApplicationᵀ)
open import QuotientedTermImprecision using
  (quotient-down-applicationᵖᵀ)


quotient-function-paired-narrowing-application-proofᵀ :
  QuotientFunctionPairedNarrowingApplicationᵀ
quotient-function-paired-narrowing-application-proofᵀ =
  quotient-down-applicationᵖᵀ
