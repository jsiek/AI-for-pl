module
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationProof
  where

-- File Charter:
--   * Proves paired-widening beta distribution from hereditary codomain
--     compatibility with the complete down-application-up QTI constructor.
--   * Splits the function square into its domain and codomain squares.
--   * Contains no postulate, hole, catch-all, or permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
import NarrowWiden as NW
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

open import QuotientedTermImprecision using
  (down·up⊑down·upᵀ; quotient-cast-widening)
open import proof.Quotient.NuImprecisionQuotientArrowComponents using
  (quotient-boundary-arrow-components)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)


source-function-cast-beta-paired-widening-function-compatible-relation-proofᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ
source-function-cast-beta-paired-widening-function-compatible-relation-proofᵀ
    {pA₀ = pA₀} {pB₀ = pB₀} {pB = pB}
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    square compatible inner argument-related
    with quotient-boundary-arrow-components square
source-function-cast-beta-paired-widening-function-compatible-relation-proofᵀ
    {pA₀ = pA₀} {pB₀ = pB₀} {pB = pB}
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    square compatible inner argument-related
    | qA , qB , refl , domain-square , codomain-square =
  down·up⊑down·upᵀ
    mode seal★ (c⊢ , cⁿ) c-shape
    mode′ seal★′ (e⊢ , eⁿ) e-shape
    inner argument-related domain-square
    (quotient-cast-widening
      mode seal★ (d⊢ , dʷ)
      mode′ seal★′ (f⊢ , fʷ))
    d-shape f-shape codomain-square
    compatible
