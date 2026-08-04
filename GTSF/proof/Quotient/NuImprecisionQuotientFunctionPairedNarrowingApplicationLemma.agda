module
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma
  where

-- File Charter:
--   * Exports quotient-function paired-narrowing application introduction.
--   * Keeps the statement separate from its implementation.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationDef
  using (QuotientFunctionPairedNarrowingApplicationᵀ)
open import
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationProof
  using (quotient-function-paired-narrowing-application-proofᵀ)


quotient-function-paired-narrowing-applicationᵀ :
  QuotientFunctionPairedNarrowingApplicationᵀ
quotient-function-paired-narrowing-applicationᵀ =
  quotient-function-paired-narrowing-application-proofᵀ
