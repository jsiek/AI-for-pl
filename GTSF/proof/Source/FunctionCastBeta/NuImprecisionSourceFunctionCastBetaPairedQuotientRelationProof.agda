module
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationProof
  where

-- File Charter:
--   * Proves quotient-paired function beta distribution with the quotient
--     retained at the application boundary.
--   * Reuses the existing quotient widening eliminator for result casts.
--   * Contains no postulate, hole, catch-all, or permissive option.

import Coercions as C
import NarrowWiden as NW
open import Data.Product using (_,_; proj₂)

open import QuotientedTermImprecision using
  ( quotient-cast-widening
  ; quotient-id-widening
  ; quotient-id-down-applicationᵖᵀ
  ; up⊑upᵀ
  )
open import
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationDef
  using (QuotientFunctionPairedNarrowingApplicationᵀ)
open import proof.Quotient.NuImprecisionQuotientArrowComponents using
  (⊑ᵖ-arrow-components)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)

source-function-cast-beta-paired-quotient-relation-proofᵀ :
  QuotientFunctionPairedNarrowingApplicationᵀ →
  SourceFunctionCastBetaPairedQuotientRelationᵀ
source-function-cast-beta-paired-quotient-relation-proofᵀ
    application {qD = qD} {pB = pB}
    inner
    (quotient-id-widening
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ)))
    argument-related =
  up⊑upᵀ application-related result-widening pB
  where
  application-related =
    quotient-id-down-applicationᵖᵀ
      {qB = proj₂ (⊑ᵖ-arrow-components qD)}
      (c⊢ , cⁿ) (e⊢ , eⁿ) inner argument-related
  result-widening =
    quotient-id-widening (d⊢ , dʷ) (f⊢ , fʷ)
source-function-cast-beta-paired-quotient-relation-proofᵀ
    application {qD = qD} {pB = pB}
    inner
    (quotient-cast-widening
      mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      mode′ seal★′
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ)))
    argument-related =
  up⊑upᵀ application-related result-widening pB
  where
  application-related =
    application
      {qB = proj₂ (⊑ᵖ-arrow-components qD)}
      mode seal★ (c⊢ , cⁿ)
      mode′ seal★′ (e⊢ , eⁿ)
      inner argument-related
  result-widening =
    quotient-cast-widening
      mode seal★ (d⊢ , dʷ)
      mode′ seal★′ (f⊢ , fʷ)
