module proof.InterpreterIndexedCoercionImmediateProof where

-- File Charter:
--   * Constructs exact operational origins for inert function and forall
--     coercions at positive fuel.
--   * Derives output typing from the unary coercion interpreter theorem.
--   * Uses only direct interpreter equations and static component inversion.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; _↦_; `∀; gen)
open import Data.Bool using (true)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (NonVar; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_; ν)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Coercion.InterpreterCoercionComputation
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterCoercionSemanticTyping
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
open import Relation.Binary.PropositionalEquality using (refl)
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

indexed-paired-function-coercion :
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
  OperationalValueNarrowing
    (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
    (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
      (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]))
    R
    (coerceValue W θ (c ↦ d) V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    (suc left-index) (suc right-index)
indexed-paired-function-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with function-coercion-components (reachable-component action)
       | component-left-applied-typing (reachable-component action)
       | component-right-applied-typing (reachable-component action)
indexed-paired-function-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | domain , codomain | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-function-computation coerce-function-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-function-computation (suc zero))))
      (paired-function-origin runtime action domain codomain value)

indexed-left-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A B C D T₁ T₂ pA pB pC pD c d V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) skip-coercion
      {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  OperationalValueNarrowing
    (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
    (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
      (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]))
    R
    (coerceValue W θ (c ↦ d) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-function-coercion
    {W = W} {θ = θ}
    runtime action value
    with left-function-coercion-components action
       | component-left-applied-typing action
indexed-left-function-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | domain , codomain | μ , left-typing =
  indexed-simulation-pointwise
    coerce-function-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
        (right-value-typed input))
      (left-function-origin runtime action domain codomain value)

indexed-right-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (c′ ↦ d′))
      {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  OperationalValueNarrowing
    (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
    (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
      (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]))
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    left-index (suc right-index)
indexed-right-function-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with right-function-coercion-components action
       | component-right-applied-typing action
indexed-right-function-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | domain , codomain | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl)
    coerce-function-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-function-computation (suc zero))))
      (right-function-components-origin
        runtime action domain codomain value)

indexed-paired-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ `∀ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (coerceValue W θ (`∀ c) V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    (suc left-index) (suc right-index)
indexed-paired-forall-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with paired-forall-coercion-component action
       | component-left-applied-typing action
       | component-right-applied-typing action
indexed-paired-forall-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | ρ′ , lift , component
    | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-forall-computation coerce-forall-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-forall-computation (suc zero))))
      (paired-forall-origin runtime action lift component value)

indexed-left-forall-coercion :
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
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ T ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ T ⟧[ θ′ ])
    R
    (coerceValue W θ (`∀ c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-forall-coercion
    {W = W} {θ = θ}
    runtime action value
    with left-forall-coercion-component action
       | component-left-applied-typing action
indexed-left-forall-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | ρ′ , lift , component | μ , left-typing =
  indexed-simulation-pointwise
    coerce-forall-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
        (right-value-typed input))
      (left-forall-origin runtime action lift component value)

indexed-right-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B′ p q c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ A} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ `∀ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ A ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    left-index (suc right-index)
indexed-right-forall-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with right-forall-coercion-component action
       | component-right-applied-typing action
indexed-right-forall-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | ρ′ , lift , component | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl) coerce-forall-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-forall-computation (suc zero))))
      (right-forall-origin runtime action lift component value)

indexed-paired-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q C C′ c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) (apply-coercion (gen C′ c′))
      {A} {A′} {`∀ B} {`∀ B′} p (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (coerceValue W θ (gen C c) V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    (suc left-index) (suc right-index)
indexed-paired-generalization-coercion
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    with component-left-applied-typing action
       | component-right-applied-typing action
indexed-paired-generalization-coercion
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′}
    runtime action value
    | μ , left-typing | μ′ , right-typing =
  indexed-simulation-pointwise
    coerce-generalization-computation
    coerce-generalization-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-generalization-computation (suc zero))))
      (paired-generalized-origin runtime action value)

indexed-left-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q C c V V′}
    {nonvar : NonVar B} {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) skip-coercion
      {A} {T} {`∀ B} {T} p (ν nonvar occ q)) →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ T ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ T ⟧[ θ′ ])
    R
    (coerceValue W θ (gen C c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-generalization-coercion
    {W = W} {θ = θ}
    runtime action value
    with component-left-applied-typing action
indexed-left-generalization-coercion
    {left-index} {right-index}
    {W = W} {θ = θ}
    runtime action value
    | μ , left-typing =
  indexed-simulation-pointwise
    coerce-generalization-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
        (right-value-typed input))
      (left-generalized-origin runtime action value)

indexed-right-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S A′ B′ p q C′ c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (gen C′ c′))
      {S} {A′} {S} {`∀ B′} p q) →
  OperationalValueNarrowing
    ⟦ S ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ S ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    left-index (suc right-index)
indexed-right-generalization-coercion
    {W′ = W′} {θ′ = θ′}
    runtime action value
    with component-right-applied-typing action
indexed-right-generalization-coercion
    {left-index} {right-index}
    {W′ = W′} {θ′ = θ′}
    runtime action value
    | μ′ , right-typing =
  indexed-simulation-pointwise
    (λ n → refl) coerce-generalization-computation
    (terminal-simulation-index
      (immediate-return-simulation result))
  where
  input = operational-typed value

  result =
    operational-value
      (typed-value-narrowing
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
          (coerce-generalization-computation (suc zero))))
      (right-generalized-origin runtime action value)
