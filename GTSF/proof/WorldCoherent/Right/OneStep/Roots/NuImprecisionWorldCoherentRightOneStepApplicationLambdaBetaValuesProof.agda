module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaValuesProof
  where

-- File Charter:
--   * Classifies a caught source function related to a target lambda as an
--     ordinary lambda or an inert function cast.
--   * Sends the ordinary-lambda case to the completed substitution root and
--     isolates the recursive source-function-cast case as one exact contract.
--   * Removes allocation prefixes while retaining the related lambda bodies.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using
  ( suc
  ; zero
  )
open import Data.Nat.Properties using (suc-injective)
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( StoreImp
  ; ctx-imp
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-ƛ
  ; ok-no
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; ƛ⊑ƛᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( forget
  ; ⊢ƛ
  )
open import Types using
  ( Ty
  ; _⇒_
  )
open import Relation.Binary.PropositionalEquality using (trans)
open import proof.DGG.Core.NuPreservation using
  ( runtime-·₁
  ; runtime-·₂
  ; value-runtime-No•
  )
open import proof.DGG.Core.NuProgress using
  ( canonical-⇒
  ; fv-ƛ
  ; fv-↦
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootDef
  using (WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ)
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof
  using (target-function-cast-spine-rank-unique)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ
  )


private
  lambda-runtime-body-No• :
    ∀ {N} →
    RuntimeOK (ƛ N) →
    No• N
  lambda-runtime-body-No• (ok-no (no•-ƛ noN)) = noN

  related-lambda-bodiesᵀ :
    ∀ {Φ Δᴸ Δᴿ N N′ A A′ B B′ pA pB}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ ƛ N ⊑ ƛ N′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ []
      ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
  related-lambda-bodiesᵀ (ƛ⊑ƛᵀ hA hA′ body) = body
  related-lambda-bodiesᵀ
      (allocation-prefixᵀ prefix inner
        (⊢ƛ hA body⊢) (⊢ƛ hA′ body′⊢)) =
    allocation-prefixᵀ prefix (related-lambda-bodiesᵀ inner)
      body⊢ body′⊢


world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ :
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ zero
world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
    lambda-root
    {L = L} {N′ = N′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    with canonical-⇒ vL
      (forget (nu-term-imprecision-source-typing function-related))
world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
    lambda-root
    {N′ = N′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-ƛ refl =
  lambda-root
    coherent exclusive unique
    vM source-argument-no
    vV′ target-argument-no
    source-body-no target-body-no
    (related-lambda-bodiesᵀ function-related)
    argument-related
  where
  source-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM)
  target-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM′)
  source-argument-no =
    value-runtime-No• vM (runtime-·₂ (ƛ _) okM)
  target-argument-no =
    value-runtime-No• vV′ (runtime-·₂ (ƛ N′) okM′)
world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
    lambda-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-↦ vV refl
    with trans
      (target-function-cast-spine-rank-unique
        (vV ⟨ _ C.↦ _ ⟩) vL)
      rank
world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
    lambda-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-↦ vV refl | ()


world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ :
  ∀ {n} →
  WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ n →
  WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ (suc n)
world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
    {n} function-cast-root
    {L = L}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    with canonical-⇒ vL
      (forget (nu-term-imprecision-source-typing function-related))
world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
    {n} function-cast-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-ƛ refl
    with trans
      (target-function-cast-spine-rank-unique (ƛ _) vL)
      rank
world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
    {n} function-cast-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-ƛ refl | ()
world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
    {n} function-cast-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ rank
    | fv-↦ vV refl =
  function-cast-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vV vM vV′ inner-rank
  where
  outer-rank =
    trans
      (target-function-cast-spine-rank-unique
        (vV ⟨ _ C.↦ _ ⟩) vL)
      rank
  inner-rank = suc-injective outer-rank
