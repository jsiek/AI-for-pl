module
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationLemma
  where

-- File Charter:
--   * Exports ordinary-function paired-narrowing application introduction.
--   * Keeps the statement separate from its implementation.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  using (OrdinaryFunctionPairedNarrowingApplicationᵀ)
open import
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationProof
  using (ordinary-function-paired-narrowing-application-proofᵀ)


ordinary-function-paired-narrowing-applicationᵀ :
  OrdinaryFunctionPairedNarrowingApplicationᵀ
ordinary-function-paired-narrowing-applicationᵀ =
  ordinary-function-paired-narrowing-application-proofᵀ
