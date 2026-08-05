module Simulation.Core.InterpreterSimulationContext where

-- File Charter:
--   * Defines the synchronized static/runtime context consumed by direct
--     interpreter simulation.
--   * Keeps world typing, store realization, term-environment typing, and
--     value narrowing in one proof-relevant configuration.
--   * Contains no evaluator recursion or reduction semantics.

open import Interpreter
open import Data.List using ([])
open import Data.Nat using (z≤n)
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Typing.InterpreterSemanticTypingCore
import Runtime.InterpreterRuntimeFrame as Frame
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing
open import ImprecisionWf using (ImpCtx)
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-empty)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

record RuntimeNarrowing
    {W W′ : World}
    (R : WorldRelation W W′)
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (θ θ′ : TypeEnvironment) : Set₁ where
  constructor runtime-narrowing
  field
    assumption-membership-unique :
      AssumptionMembershipUnique Φ

    left-world-typed :
      WorldTyping W

    right-world-typed :
      WorldTyping W′

    left-runtime-context :
      RuntimeContext W Δᴸ (NTI.leftStoreⁱ ρ) θ

    right-runtime-context :
      RuntimeContext W′ Δᴿ (NTI.rightStoreⁱ ρ) θ′

    right-runtime-environment :
      RuntimeTypeEnvironment θ′

    store-correspondences-realized :
      StoreCorrespondenceRealization R Φ Δᴸ Δᴿ ρ θ θ′

    type-environments-realized :
      TypeEnvironmentRealization R Φ θ θ′

    abstract-supply :
      nextAbstractIndex θ′ Data.Nat.≤ nextAbstractIndex θ

open RuntimeNarrowing public

runtime-narrowing-frame :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′
runtime-narrowing-frame runtime =
  Frame.runtime-frame-narrowing
    (left-runtime-context runtime)
    (right-runtime-context runtime)
    (store-correspondences-realized runtime)
    (type-environments-realized runtime)
    (abstract-supply runtime)

runtime-narrowing-from-frame :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  AssumptionMembershipUnique Φ →
  RuntimeTypeEnvironment θ′ →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′
runtime-narrowing-from-frame W⊢ W′⊢ unique runtime-env′ frame =
  runtime-narrowing unique W⊢ W′⊢
    (Frame.left-runtime-context frame)
    (Frame.right-runtime-context frame)
    runtime-env′
    (Frame.store-correspondences-realized frame)
    (Frame.type-environments-realized frame)
    (Frame.abstract-supply frame)

record EnvironmentRealization
    {W W′ : World}
    {R : WorldRelation W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′)
    (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ)
    (γ γ′ : Environment) : Set₁ where
  constructor environment-realization
  field
    environments-narrow :
      EnvironmentNarrowing R γ γ′

    left-environment-typed :
      EnvironmentTyping W θ γ (NTI.leftCtxⁱ γᵀ)

    right-environment-typed :
      EnvironmentTyping W′ θ′ γ′ (NTI.rightCtxⁱ γᵀ)

open EnvironmentRealization public

record OpenEvaluationNarrowing
    {W W′ : World}
    {R : WorldRelation W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {γ γ′ : Environment}
    {N N′ A B p}
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′)
    (environment :
      EnvironmentRealization runtime γᵀ γ γ′)
    (terms :
      OpenInterpreterTermNarrowing
        R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) : Set₁ where
  constructor open-evaluation-narrowing

empty-runtime-narrowing :
  RuntimeNarrowing
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.empty-world⊑
    [] 0 0 [] [] []
empty-runtime-narrowing =
  runtime-narrowing
    assumption-membership-unique-empty
    empty-world-typed
    empty-world-typed
    (runtime-context length-empty []-scoped store-empty)
    (runtime-context length-empty []-scoped store-empty)
    runtime-type-empty
    empty-store-correspondence-realization
    empty-type-environment-realization
    z≤n

empty-environment-realization :
  EnvironmentRealization
    empty-runtime-narrowing [] [] []
empty-environment-realization =
  environment-realization
    []⊑[]ᵉ environment-empty environment-empty
