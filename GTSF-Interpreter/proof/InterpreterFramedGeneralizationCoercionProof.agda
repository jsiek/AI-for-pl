module proof.InterpreterFramedGeneralizationCoercionProof where

-- File Charter:
--   * Constructs exact returned generalized origins at positive fuel.
--   * Derives endpoint typing from unary coercion interpretation.
--   * Uses direct interpreter equations and retained coercion evidence only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (gen)
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

indexed-framed-paired-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q C C′ c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) (apply-coercion (gen C′ c′))
      {A} {A′} {`∀ B} {`∀ B′} p (∀ⁱ q)) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (coerceValue W θ (gen C c) V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-generalization-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with component-left-applied-typing action
       | component-right-applied-typing action
indexed-framed-paired-generalization-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-generalization-computation
    coerce-generalization-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (paired-generalized-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (generalized⊑
        (paired-generalized-type-narrowing action)
        (persistent-generalized-component action
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
        (coerce-generalization-computation (suc zero)))
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero)
          (right-world-typed input)
          (right-runtime-context runtime)
          right-typing
          (right-value-typed input))
        (coerce-generalization-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (paired-generalized-origin runtime action
        (framed-value-operational value))

indexed-framed-left-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q C c V V′}
    {nonvar : NonVar B} {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) skip-coercion
      {A} {T} {`∀ B} {T} p (ν nonvar occ q)) →
  FramedValueNarrowing
    {A = A} {A′ = T} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar occ q)) R
    (coerceValue W θ (gen C c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-generalization-coercion
    {W = W} {θ = θ}
    runtime action value
    with component-left-applied-typing action
indexed-framed-left-generalization-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | μ , left-typing =
  indexed-simulation-pointwise
    coerce-generalization-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (left-generalized-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (left-generalized⊑
        (persistent-left-generalization-component action
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
        (coerce-generalization-computation (suc zero)))
      (right-value-typed input)

  output-operational =
    operational-value output-typed
      (left-generalized-origin runtime action
        (framed-value-operational value))

indexed-framed-right-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S A′ B′ p q C′ c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (gen C′ c′))
      {S} {A′} {S} {`∀ B′} p q) →
  FramedValueNarrowing
    {A = S} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    left-index (suc right-index)
indexed-framed-right-generalization-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with component-right-applied-typing action
indexed-framed-right-generalization-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl) coerce-generalization-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (right-generalized-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (right-generalized⊑
        (persistent-right-generalization-component action
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
        (coerce-generalization-computation (suc zero)))

  output-operational =
    operational-value output-typed
      (right-generalized-origin runtime action
        (framed-value-operational value))
