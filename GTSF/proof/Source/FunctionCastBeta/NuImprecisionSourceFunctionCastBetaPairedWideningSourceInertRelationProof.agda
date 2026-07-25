module
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationProof
  where

-- File Charter:
--   * Proves source-inert paired-widening beta distribution from paired
--     narrowing quotient introduction and mixed application congruence.
--   * Uses the existing quotient widening eliminator for the result casts.
--   * Contains no postulate, hole, catch-all, or permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
import NarrowWiden as NW
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

open import
  proof.NuCore.Misc.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  using (OrdinaryFunctionPairedNarrowingApplicationᵀ)
open import QuotientedTermImprecision using
  (quotient-cast-widening; up⊑upᵀ)
open import proof.Quotient.NuImprecisionQuotientArrowComponents using
  (quotient-boundary-arrow-components)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationDef
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
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    square inert inner argument-related
    with quotient-boundary-arrow-components square
source-function-cast-beta-paired-widening-source-inert-relation-proofᵀ
    application
    {pA₀ = pA₀} {pB₀ = pB₀} {pB = pB}
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    square inert inner argument-related
    | qA , qB , refl , domain-square , codomain-square =
  up⊑upᵀ
    (application
      mode seal★ (c⊢ , cⁿ) c-shape
      mode′ seal★′ (e⊢ , eⁿ) e-shape
      inner argument-related domain-square)
    (quotient-cast-widening
      mode seal★ (d⊢ , dʷ)
      mode′ seal★′ (f⊢ , fʷ))
    pB d-shape f-shape codomain-square
