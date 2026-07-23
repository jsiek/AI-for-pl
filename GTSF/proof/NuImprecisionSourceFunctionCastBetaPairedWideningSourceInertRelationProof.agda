module
  proof.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationProof
  where

-- File Charter:
--   * Proves source-inert paired-widening beta distribution from paired
--     narrowing quotient introduction and mixed application congruence.
--   * Uses the existing quotient widening eliminator for the result casts.
--   * Contains no postulate, hole, catch-all, or permissive option.

import Coercions as C
import NarrowWiden as NW
open import Data.Product using (_,_)

open import proof.ForallPermutationProperties using (⊑→⊑ᵖ)
open import
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  using (OrdinaryFunctionPairedNarrowingApplicationᵀ)
open import QuotientedTermImprecision using
  (quotient-cast-widening; up⊑upᵀ)
open import
  proof.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationDef
  using
  (SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ)


source-function-cast-beta-paired-widening-source-inert-relation-proofᵀ :
  OrdinaryFunctionPairedNarrowingApplicationᵀ →
  SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ
source-function-cast-beta-paired-widening-source-inert-relation-proofᵀ
    application
    {pA₀ = pA₀} {pB₀ = pB₀} {pB = pB}
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    inert inner argument-related =
  up⊑upᵀ application-related result-widening pB
  where
  application-related =
    application
      {qB = ⊑→⊑ᵖ pB₀}
      mode seal★ (c⊢ , cⁿ)
      mode′ seal★′ (e⊢ , eⁿ)
      inner argument-related
  result-widening =
    quotient-cast-widening
      mode seal★ (d⊢ , dʷ)
      mode′ seal★′ (f⊢ , fʷ)
