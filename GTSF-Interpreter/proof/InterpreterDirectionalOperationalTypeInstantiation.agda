module proof.InterpreterDirectionalOperationalTypeInstantiation where

-- File Charter:
--   * Proves operational paired and source-only type-abstraction
--     instantiation in each terminal direction.
--   * Uses the future-allocation certificates stored in operational origins.
--   * Contains no recursion, small-step reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (suc)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using
  ( WorldTyping
  ; instantiateSemantic
  ; nominal-type
  ; polymorphic-type
  )
open import Simulation.Core.InterpreterSimulationResult using
  (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterTypeAbstractionInstantiationHelpers using
  (type-abstraction-instantiation-computation)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-operational-type-abstraction :
  ∀ {index W W′ A A′ θ θ′ body body′ X X′ V V′}
    {R : WorldRelation W W′} →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  WorldTyping (allocate W A θ) →
  WorldTyping (allocate W′ A′ θ′) →
  (∀ {U U′ C C′ σ σ′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    WorldTyping (allocate U C σ) →
    WorldTyping (allocate U′ C′ σ′) →
    OperationalValueNarrowing
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName U))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName U′))) body′)
      (allocate-both S C~C′ σ~σ′)
      (substituteName X (freshSealName U) V)
      (substituteName X′ (freshSealName U′) V′)) →
  IndexedTerminalSimulation
    (OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-both R A~A′ θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′)
      (type-abstraction X′ V′))
    (suc index) (suc index)
paired-operational-type-abstraction
    A~A′ θ~θ′ W⊢ W′⊢ instantiate =
  indexed-simulation-pointwise
    type-abstraction-instantiation-computation
    type-abstraction-instantiation-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (instantiate extension-refl A~A′ θ~θ′ W⊢ W′⊢)))

left-operational-type-abstraction :
  ∀ {index W W′ A θ body target X V V′}
    {R : WorldRelation W W′} →
  (θ-ok : TypeEnvironmentScoped W θ) →
  WorldTyping (allocate W A θ) →
  WorldTyping W′ →
  (∀ {U U′ C σ}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped U σ) →
    WorldTyping (allocate U C σ) →
    WorldTyping U′ →
    OperationalValueNarrowing
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName U))) body)
      target
      (allocate-left-dynamic {A = C} S σ-ok)
      (substituteName X (freshSealName U) V)
      V′) →
  IndexedTerminalSimulation
    (OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      target)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (immediateReturn W′ V′)
    (suc index) (suc index)
left-operational-type-abstraction
    θ-ok W⊢ W′⊢ instantiate =
  indexed-simulation-pointwise
    type-abstraction-instantiation-computation
    (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (instantiate extension-refl θ-ok W⊢ W′⊢)))
