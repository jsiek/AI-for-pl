module proof.InterpreterFramedApplyValueProof where

-- File Charter:
--   * Dispatches positive-fuel application on exact framed value origins.
--   * Runs closure bodies and inert proxy phases through explicit callbacks.
--   * Leaves quotient observation behind one explicit callback.
--   * Uses no small-step reduction or theorem derived from it.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Framed.InterpreterFramedSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Simulation.Indexed.InterpreterIndexedFunctionProxy
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive using
  (IndexedApplyValueSimulation)
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using
  (environment-cons; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Simulation.Core.InterpreterSimulationResult using (guard)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using
  ( TypedValueNarrowing
  ; left-value-typed
  ; left-world-typed
  ; right-value-typed
  ; right-world-typed
  ; values-narrow
  )
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.InterpreterIndexedGuardSimulation using
  (paired-guard-indexed)
open import proof.InterpreterIndexedResultMap using
  (indexed-result-map)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds
open Narrowing.InterpreterTermNarrowing.InterpreterValues

closure-application-computation :
  ∀ {W N γ θ U} n →
  applyValue W (closure N γ θ) U n ≡
  guard W (interpret W (U ∷ γ) θ N) n
closure-application-computation Data.Nat.zero =
  refl
closure-application-computation (suc n) =
  refl

operational-application-framed :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  IndexedApplyValueSimulation
    (suc left-index) (suc right-index) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime U U′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W V U) (applyValue W′ V′ U′)
    (suc left-index) (suc right-index)
operational-application-framed application runtime value argument =
  indexed-result-map
    (application
      (framed-value-operational value)
      (framed-value-operational argument))
    (λ
      { R≤S operational-result →
          framed-result
            (runtime-narrowing-weaken R≤S
              (left-world-typed
                (operational-typed operational-result))
              (right-world-typed
                (operational-typed operational-result))
              runtime)
            (operationally-framed-value operational-result)
      })

indexed-framed-apply-value-positive :
  ∀ {left-index right-index} →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {N N′ : N.Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    FramedIndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  FramedIndexedCoercionSimulation left-index right-index →
  FramedIndexedCoercionSimulation left-index (suc right-index) →
  FramedIndexedCoercionSimulation (suc left-index) right-index →
  FramedIndexedApplyValueSimulation left-index right-index →
  FramedIndexedApplyValueSimulation left-index (suc right-index) →
  FramedIndexedApplyValueSimulation (suc left-index) right-index →
  IndexedApplyValueSimulation
    (suc left-index) (suc right-index) →
  (∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ B B′ V V′ U U′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {R : WorldRelation W W′} →
    AssumptionMembershipUnique Φ →
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
    TypedValueNarrowing
      ⟦ A ⇒ B ⟧[ θ ] ⟦ A′ ⇒ B′ ⟧[ θ′ ] R V V′ →
    FramedValueOrigin runtime
      (pA ImprecisionWf.↦ pB) V V′ →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = pA} runtime U U′ →
    IndexedTerminalSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc left-index) (suc right-index)) →
  FramedIndexedApplyValueSimulation
    (suc left-index) (suc right-index)
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (framed-value typed operational
      (closure-originᶠ environment origins terms))
    argument =
  indexed-simulation-pointwise
    closure-application-computation
    closure-application-computation
    (paired-guard-indexed
      (term-simulation unique runtime
        (environment-realization
          (values-narrow (framed-value-typed argument) ∷⊑∷ᵉ
           environments-narrow environment)
          (environment-cons
            (left-value-typed (framed-value-typed argument))
            (left-environment-typed environment))
          (environment-cons
            (right-value-typed (framed-value-typed argument))
            (right-environment-typed environment)))
        (argument ∷⊑∷ᶠ origins)
        terms))
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (framed-value typed operational
      (paired-function-originᶠ action domain codomain value))
    argument =
  indexed-paired-function-proxy-application
    (paired-coercion unique runtime domain argument)
    (λ
      { R≤S (framed-result runtimeS domain-value) →
          paired-application unique runtimeS
            (framed-value-narrowing-future
              {runtimeS = runtimeS} R≤S value)
            domain-value
      })
    (λ
      { R≤S (framed-result runtimeS application-value) →
          paired-coercion unique runtimeS codomain application-value
      })
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (framed-value typed operational
      (left-function-originᶠ action domain codomain value))
    argument =
  indexed-left-function-proxy-application
    (left-coercion unique runtime domain argument)
    (λ
      { R≤S (framed-result runtimeS domain-value) →
          left-application unique runtimeS
            (framed-value-narrowing-future
              {runtimeS = runtimeS} R≤S value)
            domain-value
      })
    (λ
      { R≤S (framed-result runtimeS application-value) →
          left-coercion unique runtimeS codomain application-value
      })
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (framed-value typed operational
      (right-function-originᶠ action domain codomain value))
    argument =
  indexed-right-function-proxy-application
    (right-coercion unique runtime domain argument)
    (λ
      { R≤S (framed-result runtimeS domain-value) →
          right-application unique runtimeS
            (framed-value-narrowing-future
              {runtimeS = runtimeS} R≤S value)
            domain-value
      })
    (λ
      { R≤S (framed-result runtimeS application-value) →
          right-coercion unique runtimeS codomain application-value
      })
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(reframed-value {runtime = runtime0} typed inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(reindexed-value typed inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (operationally-framed-value operational)
    argument =
  operational-application-framed
    operational-application runtime
    (operationally-framed-value operational) argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(paired-lifted-value
      unique₀ left-eq right-eq R≤S typed operational inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(paired-unlifted-value
      unique₀ typed operational inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(left-lifted-value
      unique₀ left-eq R≤S typed operational inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    value@(left-unlifted-value
      unique₀ typed operational inner)
    argument =
  operational-application-framed
    operational-application runtime value argument
indexed-framed-apply-value-positive
    term-simulation paired-coercion left-coercion right-coercion
    paired-application left-application right-application
    operational-application quotient-simulation unique runtime
    (framed-value typed operational
      origin@(quotient-originᶠ base terms frame value))
    argument =
  quotient-simulation unique runtime typed origin argument
