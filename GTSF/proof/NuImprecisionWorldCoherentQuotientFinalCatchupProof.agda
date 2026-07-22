module proof.NuImprecisionWorldCoherentQuotientFinalCatchupProof where

-- File Charter:
--   * Proves complete terminal quotient catch-up from coherent classification
--     and the two outer-inst semantic leaves.
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
open import
  proof.NuImprecisionWorldCoherentQuotientInstFunTagCatchupDef
  using (WorldCoherentQuotientInstFunTagCatchupᵀ)


world-coherent-quotient-final-catchup-proofᵀ :
  WorldCoherentQuotientClassificationᵀ →
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentQuotientInstFunTagCatchupᵀ →
  WorldCoherentQuotientFinalCatchupᵀ
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst quotient-inst-tag
    coherent exclusive wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    with classify coherent exclusive wfL vV′ noV′
      inert-d′ inert-u′ down widening final
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst quotient-inst-tag
    coherent exclusive wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    | inj₁ caught =
  caught
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst quotient-inst-tag
    coherent exclusive wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    | inj₂ (inj₁ (B , s , refl , source↠ , vVd , noVd)) =
  quotient-inst coherent exclusive wfL okV vVd noVd
    vV′ noV′ inert-d′ inert-u′ down widening
world-coherent-quotient-final-catchup-proofᵀ
    classify quotient-inst quotient-inst-tag
    coherent exclusive wfL okV
    vV′ noV′ inert-d′ inert-u′ down widening final
    | inj₂ (inj₂ (B , s , refl , source↠ , vVd , noVd)) =
  quotient-inst-tag coherent exclusive wfL okV vVd noVd
    vV′ noV′ inert-d′ inert-u′ down widening
