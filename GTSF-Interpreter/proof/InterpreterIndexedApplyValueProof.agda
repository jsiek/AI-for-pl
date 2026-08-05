module proof.InterpreterIndexedApplyValueProof where

-- File Charter:
--   * Implements positive-fuel `applyValue` simulation for exact operational
--     closures and paired or one-sided function proxies.
--   * Threads captured runtimes and environments through returned-world
--     extension before every recursive call.
--   * Recovers exact right-boundary components by semantic-head inversion.
--   * Delegates quotient-framed functions to one explicit observer callback.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Indexed.InterpreterIndexedFunctionProxy
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (guard)
open import Simulation.Core.InterpreterSimulationContextProperties
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterIndexedGuardSimulation using
  (paired-guard-indexed)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import Relation.Binary.PropositionalEquality using (sym)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

closure-application-computation :
  ∀ {W N γ θ U} n →
  applyValue W (closure N γ θ) U n ≡
  guard W (interpret W (U ∷ γ) θ N) n
closure-application-computation zero =
  refl
closure-application-computation (suc n) =
  refl

indexed-apply-value-positive :
  ∀ {left-index right-index} →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {N N′ : N.Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  IndexedCoercionSimulation left-index right-index →
  IndexedCoercionSimulation left-index (suc right-index) →
  IndexedCoercionSimulation (suc left-index) right-index →
  IndexedApplyValueSimulation left-index right-index →
  IndexedApplyValueSimulation left-index (suc right-index) →
  IndexedApplyValueSimulation (suc left-index) right-index →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    IndexedTerminalSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc left-index) (suc right-index)) →
  IndexedApplyValueSimulation
    (suc left-index) (suc right-index)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (closure-origin runtime environment origins terms))
    argument =
  indexed-simulation-pointwise
    closure-application-computation
    closure-application-computation
    (paired-guard-indexed
      (term-simulation
        runtime
        (environment-realization
          (values-narrow (operational-typed argument)
            ∷⊑∷ᵉ
           environments-narrow environment)
          (environment-cons
            (left-value-typed (operational-typed argument))
            (left-environment-typed environment))
          (environment-cons
            (right-value-typed (operational-typed argument))
            (right-environment-typed environment)))
        (argument ∷⊑∷ᵒ origins)
        terms))
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (paired-function-origin runtime action
        domain-action codomain-action value))
    argument
    =
  indexed-paired-function-proxy-application
    (paired-coercion runtime domain-action argument)
    (λ R≤S domain-value →
      paired-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      paired-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        codomain-action application-value)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (left-function-origin runtime action
        domain-action codomain-action value))
    argument
    =
  indexed-left-function-proxy-application
    (left-coercion runtime domain-action argument)
    (λ R≤S domain-value →
      left-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      left-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        codomain-action application-value)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (right-function-components-origin runtime action
        domain-action codomain-action value))
    argument
    =
  indexed-right-function-proxy-application
    (right-coercion runtime domain-action argument)
    (λ R≤S domain-value →
      right-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      right-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        codomain-action application-value)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    with right-function-coercion-components action
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    | domain-action , codomain-action =
  indexed-right-function-proxy-application
    (right-coercion runtime domain-action argument)
    (λ R≤S domain-value →
      right-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      right-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        codomain-action application-value)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    value@(operational-value typed
      (right-function-boundary-origin
        runtime action origin-value left-eq))
    argument
    with right-boundary-function-coercion-components left-eq action
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    (operational-value typed
      (right-function-boundary-origin
        runtime action origin-value left-eq))
    argument
    | S₁ , S₂ , A₁′ , B₁′ , pA , pB , pC , pD ,
      refl , refl , refl , domain-action , codomain-action =
  indexed-right-function-proxy-application
    (right-coercion runtime domain-action argument)
    (λ R≤S domain-value →
      right-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          (operational-value-type-transport
            (sym left-eq) refl origin-value))
        domain-value)
    (λ R≤S application-value →
      right-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        codomain-action application-value)
indexed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    quotient-simulation
    value@(operational-value typed
      (quotient-origin runtime base terms left-eq right-eq
        frame origin-value))
    argument =
  quotient-simulation value quotient-operational-origin argument
