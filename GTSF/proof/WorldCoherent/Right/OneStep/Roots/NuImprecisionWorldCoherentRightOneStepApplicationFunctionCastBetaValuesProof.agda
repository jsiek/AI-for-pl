module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaValuesProof
  where

-- File Charter:
--   * Classifies the caught source function in target function-cast beta.
--   * Sends rank zero to the ordinary-lambda terminal and successor rank to
--     the source-function-cast matrix at the exact inner rank.
--   * Contains no semantic recursion, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.Nat using
  ( suc
  ; zero
  )
open import Data.Nat.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality using (trans)
open import NuTerms using
  ( ƛ_
  ; _⟨_⟩
  )
open import TermTyping using (forget)
open import proof.DGG.Core.NuProgress using
  ( canonical-⇒
  ; fv-ƛ
  ; fv-↦
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof
  using (target-function-cast-spine-rank-unique)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  using
  (WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesAtᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ
  )


world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ :
  WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ zero
world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
    lambda-terminal
    {L = L}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    with canonical-⇒ vL
      (forget (nu-term-imprecision-source-typing function-related))
world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
    lambda-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-ƛ refl =
  lambda-terminal coherent exclusive unique wfL okM okM′
    function-related argument-related vM vV′ vW′
world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
    lambda-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-↦ vV refl
    with trans
      (target-function-cast-spine-rank-unique
        (vV ⟨ _ C.↦ _ ⟩) vL)
      rank
world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
    lambda-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-↦ vV refl | ()


world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ :
  ∀ {n} →
  WorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesAtᵀ
    n →
  WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ (suc n)
world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
    {n} function-cast-terminal
    {L = L}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    with canonical-⇒ vL
      (forget (nu-term-imprecision-source-typing function-related))
world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
    {n} function-cast-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-ƛ refl
    with trans
      (target-function-cast-spine-rank-unique (ƛ _) vL)
      rank
world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
    {n} function-cast-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-ƛ refl | ()
world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
    {n} function-cast-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ rank
    | fv-↦ vV refl =
  function-cast-terminal coherent exclusive unique wfL okM okM′
    function-related argument-related vV vM vV′ vW′
    (suc-injective outer-rank)
  where
  outer-rank =
    trans
      (target-function-cast-spine-rank-unique
        (vV ⟨ _ C.↦ _ ⟩) vL)
      rank
