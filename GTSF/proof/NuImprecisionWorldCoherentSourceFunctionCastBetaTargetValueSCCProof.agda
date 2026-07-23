module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueSCCProof
  where

-- File Charter:
--   * Closes the target-value/value-terminal cycle by structural recursion on
--     the exact target function-cast spine rank.
--   * Uses the target-lambda terminal at rank zero and the completed
--     positive-rank dispatcher at each successor.
--   * Leaves only the two paired value leaves as parameters and contains no
--     postulate, hole, termination pragma, or permissive option.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (trans)

open import NuTerms using (ƛ_; _⟨_⟩)
open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing)
open import TermTyping using (forget)
open import proof.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import proof.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.NuImprecisionTargetFunctionCastSpineMeasureProof using
  (target-function-cast-spine-rank-unique)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedValues)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesProof
  using
  (world-coherent-source-function-cast-beta-target-function-cast-values-suc-at-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesLemma
  using
  (world-coherent-source-function-cast-beta-target-lambda-valuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueDef
  using (WorldCoherentSourceFunctionCastBetaTargetValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueProof
  using
  (world-coherent-source-function-cast-beta-target-value-at-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueRankedDef
  using
  ( WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ
  ; WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import proof.NuProgress using
  (canonical-⇒; fv-ƛ; fv-↦)


private
  target-values-at-zero :
    WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ zero
  target-values-at-zero
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      with canonical-⇒ vL′
        (forget (nu-term-imprecision-target-typing function-related))
  target-values-at-zero
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-ƛ refl =
    world-coherent-source-function-cast-beta-target-lambda-valuesᵀ
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vR′
  target-values-at-zero
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-↦ vU refl
      with trans
        (target-function-cast-spine-rank-unique
          (vU ⟨ _ C.↦ _ ⟩) vL′)
        target-rank
  target-values-at-zero
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-↦ vU refl | ()

  target-values-at-suc :
    ∀ {n} →
    WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n →
    WorldCoherentSourceFunctionCastBetaPairedValues →
    WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ (suc n)
  target-values-at-suc {n}
      lower paired
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      with canonical-⇒ vL′
        (forget (nu-term-imprecision-target-typing function-related))
  target-values-at-suc {n}
      lower paired
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-ƛ refl
      with trans
        (target-function-cast-spine-rank-unique (ƛ _) vL′)
        target-rank
  target-values-at-suc {n}
      lower paired
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-ƛ refl | ()
  target-values-at-suc {n}
      lower paired
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank
      | fv-↦ vU refl =
    world-coherent-source-function-cast-beta-target-function-cast-values-suc-at-proofᵀ
      lower paired
      world-coherent-source-one-step-target-cast-frames
      world-coherent-source-target-keep-prependᵀ
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vU vR′
      (trans
        (target-function-cast-spine-rank-unique
          (vU ⟨ _ C.↦ _ ⟩) vL′)
        target-rank)

  target-value-schedulers-at :
    WorldCoherentRightValueCatchupPrefixᵀ →
    WorldCoherentSourceFunctionCastBetaPairedValues →
    ∀ n →
    WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ n
  target-value-schedulers-at right-catchup paired zero =
    target-values-at-zero
  target-value-schedulers-at right-catchup paired (suc n) =
    target-values-at-suc lower paired
    where
    previous = target-value-schedulers-at right-catchup paired n

    lower : WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n
    lower =
      world-coherent-source-function-cast-beta-target-value-at-proofᵀ
        right-catchup source-silent-compositionᵀ previous


world-coherent-source-function-cast-beta-target-values-scc-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaPairedValues →
  WorldCoherentSourceFunctionCastBetaTargetValuesᵀ
world-coherent-source-function-cast-beta-target-values-scc-proofᵀ
    right-catchup paired
    coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ vR′ =
  target-value-schedulers-at right-catchup paired
    (targetFunctionCastSpineRank vL′)
    coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ vR′ refl
