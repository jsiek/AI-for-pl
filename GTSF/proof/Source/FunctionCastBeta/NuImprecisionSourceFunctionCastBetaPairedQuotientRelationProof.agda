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
import CastImprecisionShape as CastShape
open import Data.Product using (_,_)

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
  (quotient-boundary-arrow-components)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)

source-function-cast-beta-paired-quotient-relation-proofᵀ :
  QuotientFunctionPairedNarrowingApplicationᵀ →
  SourceFunctionCastBetaPairedQuotientRelationᵀ
source-function-cast-beta-paired-quotient-relation-proofᵀ
    application {pB = pB}
    inner
    (quotient-id-widening
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ)))
    (CastShape.shape-fun c-shape d-shape)
    (CastShape.shape-fun e-shape f-shape)
    square
    argument-related =
  let qA , qB , components , domain-square , codomain-square =
        quotient-boundary-arrow-components square in
  up⊑upᵀ
    (quotient-id-down-applicationᵖᵀ
      (c⊢ , cⁿ) c-shape
      (e⊢ , eⁿ) e-shape
      inner components argument-related domain-square)
    (quotient-id-widening (d⊢ , dʷ) (f⊢ , fʷ))
    pB d-shape f-shape codomain-square
source-function-cast-beta-paired-quotient-relation-proofᵀ
    application {pB = pB}
    inner
    (quotient-cast-widening
      mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      mode′ seal★′
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ)))
    (CastShape.shape-fun c-shape d-shape)
    (CastShape.shape-fun e-shape f-shape)
    square
    argument-related =
  let qA , qB , components , domain-square , codomain-square =
        quotient-boundary-arrow-components square in
  up⊑upᵀ
    (application
      mode seal★ (c⊢ , cⁿ) c-shape
      mode′ seal★′ (e⊢ , eⁿ) e-shape
      inner components argument-related domain-square)
    (quotient-cast-widening
      mode seal★ (d⊢ , dʷ)
      mode′ seal★′ (f⊢ , fʷ))
    pB d-shape f-shape codomain-square
