module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesProof
  where

-- File Charter:
--   * Reduces the target function cast once and delegates the shared
--     post-target paired-quotient beta square.
--   * Derives the post-target runtime invariant from the original related
--     application before crossing the shared boundary.
--   * Contains no semantic relation implementation, postulate, hole,
--     catch-all, or permissive option.

import Coercions as C

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; keep; β-↦; pure-step; _—→[_]_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using
  (No•; Term; no•-⟨⟩; _⟨_⟩)
open import
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
  using (nu-term-imprecision-target-typing)
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  (quotient-widening-pair-prefix-proofᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bulletᵖ-proofᵀ)
open import QuotientedTermImprecision using (closeᵀ; ·⊑·ᵀ)
open import TermTyping using (forget)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using
  ( WorldCoherentSourceOneStepOutcome
  ; source-step-outcome-related
  ; source-step-outcome-source-blame
  )
open import proof.DGG.Core.NuPreservation using
  (pure-runtime-preservation; value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-·₁)
open import Types using (Ty; TyCtx)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV

  prepend-target-keep-outcome :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ L : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} {χ : StoreChange} →
    M′ —→[ keep ] N′ →
    WorldCoherentSourceOneStepOutcome
      {M = M} {M′ = N′} {L = L}
      {χ = χ} {ρ = ρ} p →
    WorldCoherentSourceOneStepOutcome
      {M = M} {M′ = M′} {L = L}
      {χ = χ} {ρ = ρ} p
  prepend-target-keep-outcome target-step
      (source-step-outcome-related result) =
    source-step-outcome-related
      (world-coherent-source-target-keep-prependᵀ target-step result)
  prepend-target-keep-outcome target-step
      (source-step-outcome-source-blame source↠blame) =
    source-step-outcome-source-blame source↠blame


world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ :
  WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ
    post-target relation-prefix coherent exclusive unique wfL wfR okM okM′
    inner widening source-shape target-shape square compatible
    argument-related vV vW vL′ vR′ =
  prepend-target-keep-outcome
    (pure-step (β-↦ vL′ vR′))
    (post-target relation-prefix coherent exclusive unique wfL wfR
      okM target-post-runtime inner widening
      source-shape target-shape square compatible
      argument-related vV vW vL′ vR′)
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
  function-related =
    closeᵀ inner⁺ widening⁺ _ source-shape target-shape square
      compatible
  application-related = ·⊑·ᵀ function-related argument-related
  target-post-runtime =
    pure-runtime-preservation wfR
      (forget (nu-term-imprecision-target-typing application-related))
      okM′ (β-↦ vL′ vR′)
