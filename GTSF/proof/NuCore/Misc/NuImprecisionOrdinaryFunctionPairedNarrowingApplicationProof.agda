module
  proof.NuCore.Misc.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationProof
  where

-- File Charter:
--   * Proves ordinary-function paired-narrowing application introduction.
--   * Uses the application-specific core quotient constructor.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import
  proof.NuCore.Misc.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  using (OrdinaryFunctionPairedNarrowingApplicationᵀ)
open import QuotientedTermImprecision using
  (ordinary-down-applicationᵖᵀ)


ordinary-function-paired-narrowing-application-proofᵀ :
  OrdinaryFunctionPairedNarrowingApplicationᵀ
ordinary-function-paired-narrowing-application-proofᵀ =
  ordinary-down-applicationᵖᵀ
