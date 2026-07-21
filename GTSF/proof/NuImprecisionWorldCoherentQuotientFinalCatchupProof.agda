module proof.NuImprecisionWorldCoherentQuotientFinalCatchupProof where

-- File Charter:
--   * Proves complete terminal quotient catch-up from coherent classification
--     and the outer-inst semantic leaf.
--   * Makes the quotient integration join strict before either canonical
--     dependency implementation is imported.
--   * Contains no classifier, instantiation, or recursive dispatcher proof.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import proof.NuImprecisionWorldCoherentQuotientClassificationDef using
  (WorldCoherentQuotientClassificationᵀ)
open import proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef using
  (WorldCoherentQuotientFinalCatchupᵀ)
open import proof.NuImprecisionWorldCoherentQuotientInstCatchupDef using
  (WorldCoherentQuotientInstCatchupᵀ)


world-coherent-quotient-final-catchup-proofᵀ :
  WorldCoherentQuotientClassificationᵀ →
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentQuotientFinalCatchupᵀ
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst coherent wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    with classify coherent wfL vV′ noV′
      inert-d′ inert-u′ down widening final
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst coherent wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    | inj₁ caught =
  caught
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst coherent wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    | inj₂ (B , s , refl , source↠ , vVd , noVd) =
  quotient-inst coherent wfL okV vVd noVd
    vV′ noV′ inert-d′ inert-u′ down widening
