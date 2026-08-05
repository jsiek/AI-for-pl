module Simulation.Indexed.InterpreterIndexedSimulationMotive where

-- File Charter:
--   * States the fuel-local motives assembled by the mutual simulation
--     driver.
--   * Keeps both observed endpoint indices explicit, including apply/skip
--     coercion actions and one-sided polymorphic instantiation.
--   * Contains no proof recursion, interpreter equation, or reduction result.

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Coercion.InterpreterCoercionSimulationMotive using
  (executeCoercionAction)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
import NuTermImprecision as NTI
import NuTerms as N
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

IndexedCoercionSimulation : StepIndex → StepIndex → Set₂
IndexedCoercionSimulation left-index right-index =
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A A′ B B′ p q left right V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right {A} {A′} {B} {B′} p q →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (executeCoercionAction W θ left V)
    (executeCoercionAction W′ θ′ right V′)
    left-index right-index

IndexedApplyValueSimulation : StepIndex → StepIndex → Set₂
IndexedApplyValueSimulation left-index right-index =
  ∀ {W W′ A A′ B B′ V V′ U U′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′ →
  OperationalValueNarrowing A A′ R U U′ →
  IndexedTerminalSimulation
    (OperationalValueResult B B′) R
    (applyValue W V U)
    (applyValue W′ V′ U′)
    left-index right-index

IndexedPairedInstantiateValueSimulation :
  StepIndex → StepIndex → Set₂
IndexedPairedInstantiateValueSimulation left-index right-index =
  ∀ {W W′ A A′ θ θ′ body body′ V V′}
    {R : WorldRelation W W′} →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  WorldTyping (allocate W A θ) →
  WorldTyping (allocate W′ A′ θ′) →
  OperationalValueNarrowing
    (polymorphic-type body) (polymorphic-type body′)
    R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-both R A~A′ θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)
    left-index right-index

IndexedLeftInstantiateValueSimulation :
  StepIndex → StepIndex → Set₂
IndexedLeftInstantiateValueSimulation left-index right-index =
  ∀ {W W′ A θ body target V V′}
    {R : WorldRelation W W′} →
  (θ-ok : TypeEnvironmentScoped W θ) →
  WorldTyping (allocate W A θ) →
  WorldTyping W′ →
  OperationalValueNarrowing
    (polymorphic-type body) target R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      target)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (immediateReturn W′ V′)
    left-index right-index

IndexedRightInstantiateValueSimulation :
  StepIndex → StepIndex → Set₂
IndexedRightInstantiateValueSimulation left-index right-index =
  ∀ {W W′ A′ θ′ source body′ V V′}
    {R : WorldRelation W W′} →
  (θ′-ok : TypeEnvironmentScoped W′ θ′) →
  WorldTyping W →
  WorldTyping (allocate W′ A′ θ′) →
  OperationalValueNarrowing
    source (polymorphic-type body′) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult source
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-right-only {A′ = A′} R θ′-ok)
    (immediateReturn W V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)
    left-index right-index

IndexedInterpreterTermSimulation :
  StepIndex →
  StepIndex →
  (Φ : ImpCtx) →
  (Δᴸ Δᴿ : TyCtx) →
  (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) →
  (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  (N N′ : N.Term) →
  (A B : Ty) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Set₂
IndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p =
  ∀ {W W′ θ θ′ γ γ′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  IndexedTerminalSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ])
    R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
    left-index right-index
