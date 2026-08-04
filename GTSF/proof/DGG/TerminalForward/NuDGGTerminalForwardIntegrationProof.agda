module proof.DGG.TerminalForward.NuDGGTerminalForwardIntegrationProof where

-- File Charter:
--   * Connects the two strict forward semantic-engine contracts through the
--     completed source-trace assembly to the public gradual DGG boundary.
--   * Accepts the two independent backward terminal contracts as parameters,
--     so no permissive implementation is imported.
--   * Specializes all three arbitrary-world terminal facts to the empty world
--     and contains no postulate, hole, or permissive option.

open import DynamicGradualGuarantee using (GradualDGG)
open import proof.DGG.Core.NuDGGClosedWorld using (empty-store-wf)
open import proof.DGG.Core.NuDGGTerminal using (terminal-components⇒gradual-dgg)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardBlameDef using
  (BackwardTargetBlameᵀ)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueDef using
  (BackwardTargetValueOrSourceBlameᵀ)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardClosedProof using
  (world-coherent-forward-source-value-closed-proofᵀ)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardProof using
  (world-coherent-forward-source-value-proofᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDef using
  (WorldCoherentRightValueCatchupᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef using
  (WorldCoherentRightValueCatchupCases)
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedFramesDef
  using (WorldCoherentRightPairedFramesᵀ)
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesProof
  using (world-coherent-right-value-catchup-cases-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDispatcherProof
  using (world-coherent-right-value-catchup-dispatcher-proofᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupProof using
  (world-coherent-right-value-catchup-proofᵀ)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationLeftStepDef using
  (WorldCoherentSourceApplicationLeftStepᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceApplicationPureRootCases)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesLemma
  using (world-coherent-source-application-pure-root-cases-lemmaᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma
  using (quotient-function-paired-narrowing-applicationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationLemma
  using (source-function-cast-beta-paired-quotient-relationᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-quotient-valuesᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationLemma
  using
  (source-function-cast-beta-paired-widening-function-compatible-relationᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-widening-valuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesLemma
  using
  (world-coherent-source-function-cast-beta-paired-widening-function-compatible-valuesᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingLemma
  using (world-coherent-source-lambda-beta-schedulingᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootProof
  using (world-coherent-source-application-pure-root-proofᵀ)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationRightStepDef using
  (WorldCoherentSourceApplicationRightStepᵀ)
open import proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceCastFrameStepDef using
  (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  (WorldCoherentSourceOneStepCases)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepCasesProof using
  (world-coherent-source-one-step-cases-proofᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepDispatcherProof using
  (world-coherent-source-one-step-dispatcher-proofᵀ)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepProof using
  (world-coherent-source-one-step-proofᵀ)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveLeftStepDef using
  (WorldCoherentSourcePrimitiveLeftStepᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef using
  (WorldCoherentSourcePrimitiveRightStepᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
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
  WorldCoherentRightPairedFramesᵀ →
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
    target-casts paired-frames quotient source-all target-bullet
    target-allocation application-root-cases bullet-root cast-root
    allocation-step application-left-step application-right-step
    cast-frame-step ν-frame-step primitive-left-step primitive-right-step
    backward-value backward-blame =
  forward-case-builders-and-backward-terminals⇒gradual-dgg
    (world-coherent-right-value-catchup-cases-proofᵀ
      target-casts paired-frames quotient source-all target-bullet
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
  function-compatible-relation =
    source-function-cast-beta-paired-widening-function-compatible-relationᵀ
  quotient-relation =
    source-function-cast-beta-paired-quotient-relationᵀ
      quotient-function-paired-narrowing-applicationᵀ
  paired-function-compatible =
    world-coherent-source-function-cast-beta-paired-widening-function-compatible-valuesᵀ
      function-compatible-relation
  paired-widening =
    world-coherent-source-function-cast-beta-paired-widening-valuesᵀ
      paired-function-compatible
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
