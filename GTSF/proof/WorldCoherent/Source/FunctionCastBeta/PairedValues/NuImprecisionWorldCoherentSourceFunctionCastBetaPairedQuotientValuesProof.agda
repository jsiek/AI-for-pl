module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesProof
  where

-- File Charter:
--   * Proves the world-coherent paired-quotient beta leaf from its pure
--     beta-distributed term-imprecision relation.
--   * Handles quotient/store-prefix transport and synchronizes both beta
--     steps.
--   * Contains no semantic relation implementation, postulate, hole,
--     catch-all, or permissive option.

import Coercions as C

open import NuReduction using (β-↦; pure-step)
open import NuTerms using
  (No•; no•-⟨⟩; _⟨_⟩)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  (quotient-widening-pair-prefix-proofᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bulletᵖ-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ)
open import proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; value-runtime-No•)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ :
  SourceFunctionCastBetaPairedQuotientRelationᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ
    relation relation-prefix coherent exclusive unique wfR okM okM′
    inner widening argument-related vV vW vL′ vR′ =
  world-coherent-source-target-keep-prependᵀ
    (pure-step (β-↦ vL′ vR′))
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
  where
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vL′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-L-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bulletᵖ-proofᵀ
      relation-prefix source-V-no target-L-no inner
  widening⁺ =
    quotient-widening-pair-prefix-proofᵀ relation-prefix widening
  final-related = relation inner⁺ widening⁺ argument-related
