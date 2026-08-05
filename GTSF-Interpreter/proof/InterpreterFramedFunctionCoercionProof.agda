module proof.InterpreterFramedFunctionCoercionProof where

-- File Charter:
--   * Constructs exact returned function-proxy origins at positive fuel.
--   * Derives endpoint typing from unary coercion interpretation.
--   * Uses direct interpreter equations and static component inversion only.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (_↦_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Coercion.InterpreterCoercionComputation
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterCoercionSemanticTyping
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational; framed-value-typed)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing using
  ( ReachableComponentCoercionNarrowing
  ; reachable-component
  )
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import Runtime.InterpreterTypeEnvironmentRealization as TER
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
import NuTermImprecision as NTI
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterTypedSimulationProof using
  (returned-value-typing)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module CoercionWorldProperties =
  WorldProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing

indexed-framed-paired-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ C C′ D D′ pA pB pC pD
      c d c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) (apply-coercion (c′ ↦ d′))
      {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (coerceValue W θ (c ↦ d) V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-function-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with function-coercion-components (reachable-component action)
       | component-left-applied-typing (reachable-component action)
       | component-right-applied-typing (reachable-component action)
indexed-framed-paired-function-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | domain , codomain | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-function-computation coerce-function-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (paired-function-originᶠ
              action domain codomain value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (function-proxy⊑
        (persistent-component-coercion domain
          (runtime-narrowing-frame runtime))
        (persistent-component-coercion codomain
          (runtime-narrowing-frame runtime))
        (TER.environments-narrow
          (type-environments-realized runtime))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (left-world-typed input)
          (left-runtime-context runtime)
          left-typing
          (left-value-typed input))
        (coerce-function-computation (suc zero)))
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (right-world-typed input)
          (right-runtime-context runtime)
          right-typing
          (right-value-typed input))
        (coerce-function-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (paired-function-origin runtime action domain codomain
        (framed-value-operational value))

indexed-framed-left-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A B C D T₁ T₂ pA pB pC pD c d V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) skip-coercion
      {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = T₁ ⇒ T₂}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (coerceValue W θ (c ↦ d) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-function-coercion
    {W = W} {θ = θ}
    runtime action value
    with left-function-coercion-components action
       | component-left-applied-typing action
indexed-framed-left-function-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | domain , codomain | μ , left-typing =
  indexed-simulation-pointwise
    coerce-function-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (left-function-originᶠ
              action domain codomain value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (left-function-proxy⊑
        (persistent-left-function-component action
          (runtime-narrowing-frame runtime))
        (CoercionWorldProperties.type-environment-left-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (left-world-typed input)
          (left-runtime-context runtime)
          left-typing
          (left-value-typed input))
        (coerce-function-computation (suc zero)))
      (right-value-typed input)

  output-operational =
    operational-value output-typed
      (left-function-origin runtime action domain codomain
        (framed-value-operational value))

indexed-framed-right-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (c′ ↦ d′))
      {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = S₁ ⇒ S₂} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    left-index (suc right-index)
indexed-framed-right-function-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with right-function-coercion-components action
       | component-right-applied-typing action
indexed-framed-right-function-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | domain , codomain | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl) coerce-function-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (right-function-originᶠ
              action domain codomain value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (right-function-proxy⊑
        (persistent-right-function-component action
          (runtime-narrowing-frame runtime))
        (CoercionWorldProperties.type-environment-right-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (left-value-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (right-world-typed input)
          (right-runtime-context runtime)
          right-typing
          (right-value-typed input))
        (coerce-function-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (right-function-components-origin
        runtime action domain codomain
        (framed-value-operational value))
