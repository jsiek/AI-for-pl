module proof.InterpreterCoercionDynamicSealSimulationProof where

-- File Charter:
--   * EXPERIMENTAL Milestone 5 proof of typed source-only dynamic seal and
--     unseal simulation; this module is currently blocked by O34.
--   * Uses direct coercion equations, unary typing, and static realization.
--   * The missing ingredient is a suspended-to-ready typing bridge: the left
--     environment may contain abstract names, while active coercion soundness
--     correctly requires an all-seal `RuntimeTypeEnvironment`.
--   * Contains no small-step reduction or reduction-derived result.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Coercions renaming
  (seal to sealᶜ; unseal to unsealᶜ)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; tagˣ)
open import Interpreter
open import Typing.InterpreterCoercionSemanticTyping
open import Simulation.Coercion.InterpreterDynamicSealValueElimination
open import Narrowing.InterpreterSealNarrowing
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Runtime.InterpreterTypeEnvironmentRealizationProperties
open import Simulation.Core.InterpreterTypedSimulation
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterValueNarrowing using
  (NotSealed; tagged-not-sealed)
import NuTermImprecision as NTI
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

immediate-value-typing :
  ∀ {W V A} →
  WorldTyping W →
  ValueTyping W V A →
  ∀ n →
  OutcomeTyping W A (immediateReturn W V n)
immediate-value-typing W⊢ V⊢ zero =
  timeout-typed world-extension-refl
immediate-value-typing W⊢ V⊢ (suc n) =
  return-typed world-extension-refl W⊢ V⊢

dynamic-value-not-sealed :
  ∀ {W V} →
  ValueTyping W V dynamic-type →
  NotSealed V
dynamic-value-not-sealed
    (tagged-typed W⊢ runtime runtime-ground environment cast V⊢) =
  tagged-not-sealed

left-dynamic-seal-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A X μ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ sealᶜ A X ∶ A =⇒ ＇ X →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ) →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ ★ ⟧[ θ′ ] R V V′ →
  TerminalSimulation
    (TypedValueResult ⟦ ＇ X ⟧[ θ ] ⟦ ★ ⟧[ θ′ ])
    R
    (coerceValue W θ (sealᶜ A X) V)
    (immediateReturn W′ V′)
left-dynamic-seal-coercion-simulation runtime
    cast@(cast-seal hA X∈Σ allowed) p
    (tagˣ assumption-at X<Δᴸ) V~V′
    with store-environment-lookup
      (store-typing (left-runtime-context runtime)) X∈Σ
left-dynamic-seal-coercion-simulation runtime
    cast@(cast-seal hA X∈Σ allowed) p
    (tagˣ assumption-at X<Δᴸ) V~V′
    | α , lookup-eq , representation =
  typed-result-simulation
    (left-dynamic-seal-simulation
      lookup-eq dynamic
      (dynamic-value-not-sealed
        (right-value-typed V~V′))
      (values-narrow V~V′))
    (λ n →
      coerceValue-preserves-semantic-typing n
        (left-world-typed runtime)
        (left-runtime-context runtime)
        cast (left-value-typed V~V′))
    (immediate-value-typing
      (right-world-typed runtime)
      (right-value-typed V~V′))
  where
  dynamic =
    source-dynamic-seal-lookup
      (realizes-assumption
        (type-environments-realized runtime) assumption-at)
      lookup-eq

left-dynamic-unseal-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A X μ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ unsealᶜ X A ∶ ＇ X =⇒ A →
  (p : Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  TypedValueNarrowing
    ⟦ ＇ X ⟧[ θ ] ⟦ ★ ⟧[ θ′ ] R V V′ →
  TerminalSimulation
    (TypedValueResult ⟦ A ⟧[ θ ] ⟦ ★ ⟧[ θ′ ])
    R
    (coerceValue W θ (unsealᶜ X A) V)
    (immediateReturn W′ V′)
left-dynamic-unseal-coercion-simulation
    {W = W} {θ = θ} {X = X} {V = V} runtime
    cast@(cast-unseal hA X∈Σ allowed)
    (tagˣ assumption-at X<Δᴸ) q V~V′
    with store-environment-lookup
      (store-typing (left-runtime-context runtime)) X∈Σ
left-dynamic-unseal-coercion-simulation
    {W = W} {θ = θ} {X = X} {V = V} runtime
    cast@(cast-unseal hA X∈Σ allowed)
    (tagˣ assumption-at X<Δᴸ) q V~V′
    | expected , lookup-eq , representation
    with subst (ValueTyping W V)
      (semantic-type-name-lookup
        {θ = θ} {X = X} lookup-eq)
      (left-value-typed V~V′)
left-dynamic-unseal-coercion-simulation
    {W = W} {θ = θ} {X = X} {V = V} runtime
    cast@(cast-unseal hA X∈Σ allowed)
    (tagˣ assumption-at X<Δᴸ) q V~V′
    | expected , lookup-eq , representation
    | sealed-typed sealed-W⊢ sealed-runtime sealed-environment
        sealed-cast sealed-lookup sealed-representation U⊢ =
  typed-result-simulation
    (left-dynamic-unseal-simulation
      lookup-eq dynamic refl payloads-narrow)
    (λ n →
      coerceValue-preserves-semantic-typing n
        (left-world-typed runtime)
        (left-runtime-context runtime)
        cast (left-value-typed V~V′))
    (immediate-value-typing
      (right-world-typed runtime)
      (right-value-typed V~V′))
  where
  dynamic =
    source-dynamic-seal-lookup
      (realizes-assumption
        (type-environments-realized runtime) assumption-at)
      lookup-eq

  payloads-narrow =
    left-dynamic-sealed-payloads
      dynamic (values-narrow V~V′)
