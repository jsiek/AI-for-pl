module proof.InterpreterFramedForallCoercionProof where

-- File Charter:
--   * Constructs exact returned forall-proxy origins at positive fuel.
--   * Derives endpoint typing from unary coercion interpretation.
--   * Uses direct interpreter equations and static component inversion only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (`∀)
open import Data.Bool using (true)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (NonVar; _∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
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

indexed-framed-paired-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (coerceValue W θ (`∀ c) V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-forall-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with paired-forall-coercion-component action
       | component-left-applied-typing action
       | component-right-applied-typing action
indexed-framed-paired-forall-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | ρ′ , lift , component
    | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-forall-computation coerce-forall-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (paired-forall-originᶠ
              action lift component value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (forall-proxy⊑
        (persistent-forall-component action
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
        (coerce-forall-computation (suc zero)))
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (right-world-typed input)
          (right-runtime-context runtime)
          right-typing
          (right-value-typed input))
        (coerce-forall-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (paired-forall-origin runtime action lift component
        (framed-value-operational value))

indexed-framed-left-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q c V V′}
    {nonvar : NonVar A} {occ : occurs zero A ≡ true}
    {nonvar′ : NonVar B} {occ′ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) skip-coercion
      {`∀ A} {T} {`∀ B} {T}
      (ν nonvar occ p) (ν nonvar′ occ′ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = T}
    {p = ν nonvar occ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar′ occ′ q)) R
    (coerceValue W θ (`∀ c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-forall-coercion
    {W = W} {θ = θ}
    runtime action value
    with left-forall-coercion-component action
       | component-left-applied-typing action
indexed-framed-left-forall-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | ρ′ , lift , component | μ , left-typing =
  indexed-simulation-pointwise
    coerce-forall-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (left-forall-originᶠ
              action lift component value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (left-forall-proxy⊑
        (persistent-left-forall-component action
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
        (coerce-forall-computation (suc zero)))
      (right-value-typed input)

  output-operational =
    operational-value output-typed
      (left-forall-origin runtime action lift component
        (framed-value-operational value))

indexed-framed-right-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B′ p q c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ A} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    left-index (suc right-index)
indexed-framed-right-forall-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with right-forall-coercion-component action
       | component-right-applied-typing action
indexed-framed-right-forall-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | ρ′ , lift , component | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl) coerce-forall-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (right-forall-originᶠ
              action lift component value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (right-forall-proxy⊑
        (persistent-right-forall-component action
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
        (coerce-forall-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (right-forall-origin runtime action lift component
        (framed-value-operational value))
