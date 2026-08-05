module proof.InterpreterOperationalValueNarrowingProof where

-- File Charter:
--   * Proves related-world weakening for operational values and environments.
--   * Weakens every retained runtime producer certificate in lockstep.
--   * Contains no interpreter call or reduction result.

open import Narrowing.InterpreterOperationalValueNarrowing
import Narrowing.InterpreterCoercionNarrowing as ICN
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame-weaken)
open import Typing.InterpreterSemanticTypingCore using (WorldTyping)
open import Simulation.Core.InterpreterSimulationContextProperties using
  (environment-realization-weaken; runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowingProperties using
  (typed-value-narrowing-weaken)
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module OperationalWorldProperties =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

mutual

  operational-value-narrowing-weaken :
    ∀ {W W′ U U′ A B V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    WorldTyping U →
    WorldTyping U′ →
    OperationalValueNarrowing A B R V V′ →
    OperationalValueNarrowing A B S V V′
  operational-value-narrowing-weaken R≤S U⊢ U′⊢
      (operational-value typed origin) =
    operational-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-origin-weaken R≤S U⊢ U′⊢ origin)

  operational-value-origin-weaken :
    ∀ {W W′ U U′ A B V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    WorldTyping U →
    WorldTyping U′ →
    OperationalValueOrigin A B R V V′ →
    OperationalValueOrigin A B S V V′
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (closure-origin runtime environment origins terms) =
    closure-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      (environment-realization-weaken R≤S U⊢ U′⊢ environment)
      (operational-environment-narrowing-weaken R≤S U⊢ U′⊢ origins)
      (open-interpreter-narrowing-world-weaken R≤S terms)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      constant-origin =
    constant-origin
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-tag-origin runtime action value) =
    paired-tag-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-tag-origin runtime action value) =
    left-tag-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-tag-origin runtime action value) =
    right-tag-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-seal-origin runtime action value) =
    paired-seal-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-seal-origin runtime action value) =
    left-seal-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-function-origin runtime action domain codomain value) =
    paired-function-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action domain codomain
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-function-origin runtime action domain codomain value) =
    left-function-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action domain codomain
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-function-origin runtime action value) =
    right-function-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-function-components-origin
        runtime action domain codomain value) =
    right-function-components-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action domain codomain
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-function-boundary-origin runtime action value left-eq) =
    right-function-boundary-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
      left-eq
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-type-abstraction-origin instantiate) =
    paired-type-abstraction-origin
      λ S≤T C~C′ σ~σ′ T⊢ T′⊢ →
        instantiate
          (OperationalWorldProperties.world-extension-trans R≤S S≤T)
          C~C′ σ~σ′ T⊢ T′⊢
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-type-abstraction-origin instantiate) =
    left-type-abstraction-origin
      λ S≤T σ-ok T⊢ T′⊢ →
        instantiate
          (OperationalWorldProperties.world-extension-trans R≤S S≤T)
          σ-ok T⊢ T′⊢
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-name-instantiated-origin Q≤R α-ok result-eq value) =
    left-name-instantiated-origin
      (OperationalWorldProperties.world-extension-trans Q≤R R≤S)
      (OperationalWorldProperties.allocated-left-weaken R≤S α-ok)
      result-eq value
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-forall-origin runtime action lift component value) =
    paired-forall-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action lift component
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-forall-origin runtime action lift component value) =
    left-forall-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action lift component
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-forall-origin runtime action lift component value) =
    right-forall-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action lift component
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (paired-generalized-origin runtime action value) =
    paired-generalized-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (left-generalized-origin runtime action value) =
    left-generalized-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (right-generalized-origin runtime action value) =
    right-generalized-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      action
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (operational-quotient-origin
        runtime D⊑E alignment down up left-eq right-eq frame value) =
    operational-quotient-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      D⊑E alignment down up
      left-eq right-eq
      (quotient-value-frame-weaken R≤S frame)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  operational-value-origin-weaken R≤S U⊢ U′⊢
      (quotient-origin runtime base terms left-eq right-eq frame value) =
    quotient-origin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      (open-interpreter-narrowing-world-weaken R≤S base)
      (open-interpreter-narrowing-world-weaken R≤S terms)
      left-eq right-eq
      (quotient-value-frame-weaken R≤S frame)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)

  operational-environment-narrowing-weaken :
    ∀ {W W′ U U′ Φ Δᴸ Δᴿ θ θ′ γᵀ γ γ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    WorldTyping U →
    WorldTyping U′ →
    OperationalEnvironmentNarrowing
      θ θ′ R {Φ} {Δᴸ} {Δᴿ} γᵀ γ γ′ →
    OperationalEnvironmentNarrowing
      θ θ′ S γᵀ γ γ′
  operational-environment-narrowing-weaken R≤S U⊢ U′⊢
      []⊑[]ᵒ =
    []⊑[]ᵒ
  operational-environment-narrowing-weaken R≤S U⊢ U′⊢
      (value ∷⊑∷ᵒ environment) =
    operational-value-narrowing-weaken R≤S U⊢ U′⊢ value
      ∷⊑∷ᵒ
    operational-environment-narrowing-weaken R≤S U⊢ U′⊢
      environment
