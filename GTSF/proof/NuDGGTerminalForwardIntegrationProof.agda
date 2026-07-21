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
open import proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupProof using
  (world-coherent-right-value-catchup-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  (WorldCoherentSourceOneStepCases)
open import proof.NuImprecisionWorldCoherentSourceOneStepDispatcherProof using
  (world-coherent-source-one-step-dispatcher-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepProof using
  (world-coherent-source-one-step-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixProof using
  (world-coherent-exact-source-one-step-prefix-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentExactSourceOneStepSimulationᵀ)


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


exact-forward-engines-and-backward-terminals⇒gradual-dgg :
  WorldCoherentExactSourceOneStepSimulationᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  BackwardTargetValueOrSourceBlameᵀ →
  BackwardTargetBlameᵀ →
  GradualDGG
exact-forward-engines-and-backward-terminals⇒gradual-dgg
    exact-one-step right-prefix backward-value backward-blame =
  forward-engines-and-backward-terminals⇒gradual-dgg
    (world-coherent-source-one-step-proofᵀ exact-one-step)
    (world-coherent-right-value-catchup-proofᵀ right-prefix)
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
  exact-forward-engines-and-backward-terminals⇒gradual-dgg
    (world-coherent-exact-source-one-step-prefix-proofᵀ source-prefix)
    right-prefix backward-value backward-blame


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
