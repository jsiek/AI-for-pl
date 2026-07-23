module proof.NuDGGTerminalForwardIntegrationProof where

-- File Charter:
--   * Connects the two strict forward semantic-engine contracts through the
--     completed source-trace assembly to the public gradual DGG boundary.
--   * Accepts the two independent backward terminal contracts as parameters,
--     so no permissive implementation is imported.
--   * Specializes all three arbitrary-world terminal facts to the empty world
--     and contains no postulate, hole, or permissive option.

open import DynamicGradualGuarantee using (GradualDGG)
open import proof.NuDGGClosedWorld using (empty-store-wf)
open import proof.NuDGGTerminal using (terminal-components⇒gradual-dgg)
open import proof.NuDGGTerminalBackwardBlameDef using
  (BackwardTargetBlameᵀ)
open import proof.NuDGGTerminalBackwardValueDef using
  (BackwardTargetValueOrSourceBlameᵀ)
open import proof.NuDGGTerminalForwardClosedProof using
  (world-coherent-forward-source-value-closed-proofᵀ)
open import proof.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import proof.NuDGGTerminalForwardProof using
  (world-coherent-forward-source-value-proofᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupDef using
  (WorldCoherentRightValueCatchupᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupCasesDef using
  (WorldCoherentRightValueCatchupCases)
open import
  proof.NuImprecisionWorldCoherentRightPairedCastFrameDef using
  (WorldCoherentRightPairedCastFrameᵀ)
open import
  proof.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import proof.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupCasesProof
  using (world-coherent-right-value-catchup-cases-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupDispatcherProof
  using (world-coherent-right-value-catchup-dispatcher-proofᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupProof using
  (world-coherent-right-value-catchup-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceApplicationPureRootCases)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesLemma
  using (world-coherent-source-application-pure-root-cases-lemmaᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationLemma
  using (ordinary-function-paired-narrowing-applicationᵀ)
open import
  proof.NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma
  using (quotient-function-paired-narrowing-applicationᵀ)
open import
  proof.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationLemma
  using (source-function-cast-beta-paired-quotient-relationᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-quotient-valuesᵀ)
open import
  proof.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationLemma
  using
  (source-function-cast-beta-paired-widening-source-inert-relationᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-widening-valuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-widening-source-inert-valuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingLemma
  using (world-coherent-source-lambda-beta-schedulingᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootProof
  using (world-coherent-source-application-pure-root-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  (WorldCoherentSourceOneStepCases)
open import proof.NuImprecisionWorldCoherentSourceOneStepCasesProof using
  (world-coherent-source-one-step-cases-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepDispatcherProof using
  (world-coherent-source-one-step-dispatcher-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepProof using
  (world-coherent-source-one-step-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
  using (WorldCoherentSourceRuntimeBulletPureRootᵀ)


world-coherent-forward-and-backward-terminals⇒gradual-dgg :
  WorldCoherentForwardSourceValueᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
world-coherent-forward-and-backward-terminals⇒gradual-dgg
    forward backward-value backward-blame =
  terminal-components⇒gradual-dgg
    (world-coherent-forward-source-value-closed-proofᵀ forward)
    (λ okN okN′ N⊑N′ →
      backward-value
        empty-store-wf empty-store-wf okN okN′ N⊑N′)
    (λ okN okN′ N⊑N′ →
      backward-blame
        empty-store-wf empty-store-wf okN okN′ N⊑N′)


forward-engines-and-backward-terminals⇒gradual-dgg :
  WorldCoherentSourceOneStepSimulationᵀ →
  WorldCoherentRightValueCatchupᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
forward-engines-and-backward-terminals⇒gradual-dgg
    one-step right-value backward-value backward-blame =
  world-coherent-forward-and-backward-terminals⇒gradual-dgg
    (world-coherent-forward-source-value-proofᵀ
      one-step right-value)
    backward-value
    backward-blame


prefix-forward-engines-and-backward-terminals⇒gradual-dgg :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
prefix-forward-engines-and-backward-terminals⇒gradual-dgg
    source-prefix right-prefix backward-value backward-blame =
  forward-engines-and-backward-terminals⇒gradual-dgg
    (world-coherent-source-one-step-proofᵀ source-prefix)
    (world-coherent-right-value-catchup-proofᵀ right-prefix)
    backward-value backward-blame


source-cases-and-right-prefix⇒gradual-dgg :
  WorldCoherentSourceOneStepCases →
  WorldCoherentRightValueCatchupPrefixᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
source-cases-and-right-prefix⇒gradual-dgg
    source-cases right-prefix backward-value backward-blame =
  prefix-forward-engines-and-backward-terminals⇒gradual-dgg
    (world-coherent-source-one-step-dispatcher-proofᵀ source-cases)
    right-prefix backward-value backward-blame


forward-cases-and-backward-terminals⇒gradual-dgg :
  WorldCoherentSourceOneStepCases →
  WorldCoherentRightValueCatchupCases →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
forward-cases-and-backward-terminals⇒gradual-dgg
    source-cases right-cases backward-value backward-blame =
  source-cases-and-right-prefix⇒gradual-dgg
    source-cases
    (world-coherent-right-value-catchup-dispatcher-proofᵀ right-cases)
    backward-value backward-blame


forward-case-builders-and-backward-terminals⇒gradual-dgg :
  WorldCoherentRightValueCatchupCases →
  WorldCoherentSourceApplicationPureRootCases →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourceAllocationStepᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ →
  WorldCoherentSourceApplicationRightStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
forward-case-builders-and-backward-terminals⇒gradual-dgg
    right-cases application-root-cases bullet-root cast-root
    allocation-step application-left-step application-right-step
    cast-frame-step ν-frame-step primitive-left-step primitive-right-step
    backward-value backward-blame =
  forward-cases-and-backward-terminals⇒gradual-dgg
    (world-coherent-source-one-step-cases-proofᵀ
      (world-coherent-right-value-catchup-dispatcher-proofᵀ right-cases)
      (world-coherent-source-application-pure-root-proofᵀ
        application-root-cases)
      bullet-root cast-root
      allocation-step application-left-step application-right-step
      cast-frame-step ν-frame-step
      primitive-left-step primitive-right-step)
    right-cases backward-value backward-blame


remaining-forward-capabilities-and-backward-terminals⇒gradual-dgg :
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightPairedCastFrameᵀ →
  WorldCoherentRightQuotientDownUpFrame →
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetBulletClosingᵀ →
  WorldCoherentRightTargetAllocationFrames →
  WorldCoherentSourceApplicationPureRootCases →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourceAllocationStepᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ →
  WorldCoherentSourceApplicationRightStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
remaining-forward-capabilities-and-backward-terminals⇒gradual-dgg
    target-casts paired-cast quotient source-all target-bullet
    target-allocation application-root-cases bullet-root cast-root
    allocation-step application-left-step application-right-step
    cast-frame-step ν-frame-step primitive-left-step primitive-right-step
    backward-value backward-blame =
  forward-case-builders-and-backward-terminals⇒gradual-dgg
    (world-coherent-right-value-catchup-cases-proofᵀ
      target-casts paired-cast quotient source-all target-bullet
      target-allocation)
    application-root-cases bullet-root cast-root allocation-step
    application-left-step application-right-step cast-frame-step ν-frame-step
    primitive-left-step primitive-right-step backward-value backward-blame


scheduled-lambda-forward-builders-and-backward-terminals⇒gradual-dgg :
  WorldCoherentRightValueCatchupCases →
  WorldCoherentSourceLambdaBetaSchedulingᵀ →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourceAllocationStepᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ →
  WorldCoherentSourceApplicationRightStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
scheduled-lambda-forward-builders-and-backward-terminals⇒gradual-dgg
    right-cases schedule-lambda
    bullet-root cast-root
    allocation-step application-left-step application-right-step
    cast-frame-step ν-frame-step primitive-left-step primitive-right-step
    backward-value backward-blame =
  forward-case-builders-and-backward-terminals⇒gradual-dgg
    right-cases
    (world-coherent-source-application-pure-root-cases-lemmaᵀ
      schedule-lambda right-prefix paired-widening paired-quotient)
    bullet-root cast-root allocation-step application-left-step
    application-right-step cast-frame-step ν-frame-step
    primitive-left-step primitive-right-step backward-value backward-blame
  where
  right-prefix =
    world-coherent-right-value-catchup-dispatcher-proofᵀ right-cases
  source-inert-relation =
    source-function-cast-beta-paired-widening-source-inert-relationᵀ
      ordinary-function-paired-narrowing-applicationᵀ
  quotient-relation =
    source-function-cast-beta-paired-quotient-relationᵀ
      quotient-function-paired-narrowing-applicationᵀ
  paired-source-inert =
    world-coherent-source-function-cast-beta-paired-widening-source-inert-valuesᵀ
      source-inert-relation
  paired-widening =
    world-coherent-source-function-cast-beta-paired-widening-valuesᵀ
      paired-source-inert
  paired-quotient =
    world-coherent-source-function-cast-beta-paired-quotient-valuesᵀ
      quotient-relation


lambda-beta-assembled-and-backward-terminals⇒gradual-dgg :
  WorldCoherentRightValueCatchupCases →
  WorldCoherentSourceRuntimeBulletPureRootᵀ →
  WorldCoherentSourceCastPureRootᵀ →
  WorldCoherentSourceAllocationStepᵀ →
  WorldCoherentSourceApplicationLeftStepᵀ →
  WorldCoherentSourceApplicationRightStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ →
  WorldCoherentSourcePrimitiveLeftStepᵀ →
  WorldCoherentSourcePrimitiveRightStepᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
lambda-beta-assembled-and-backward-terminals⇒gradual-dgg
    right-cases
    bullet-root cast-root allocation-step application-left-step
    application-right-step cast-frame-step ν-frame-step
    primitive-left-step primitive-right-step backward-value backward-blame =
  scheduled-lambda-forward-builders-and-backward-terminals⇒gradual-dgg
    right-cases
    (world-coherent-source-lambda-beta-schedulingᵀ right-prefix)
    bullet-root cast-root
    allocation-step application-left-step
    application-right-step cast-frame-step ν-frame-step
    primitive-left-step primitive-right-step backward-value backward-blame
  where
  right-prefix =
    world-coherent-right-value-catchup-dispatcher-proofᵀ right-cases
