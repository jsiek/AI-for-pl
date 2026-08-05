module proof.InterpreterErrorFreedomCore where

-- File Charter:
--   * Implements the generic semantic-typing and error-freedom consequences
--     for the direct fuel-indexed interpreter.
--   * Keeps the proof implementation below the public theorem interface.
--   * Depends only on interpreter syntax and typing, never on reduction.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Narrowing.InterpreterWorldNarrowing using ([]-scoped)
import NuTerms as N
open import proof.InterpreterTypingCore
open import Types

outcome-typing-excludes-error :
  ∀ {W A o U e} →
  OutcomeTyping W A o →
  o ≢ failed U e
outcome-typing-excludes-error (timeout-typed W≤T) ()
outcome-typing-excludes-error (blame-typed W≤T) ()
outcome-typing-excludes-error (return-typed W≤T T⊢ V⊢) ()

interpret-never-fails :
  ∀ n {W Δ Σ Γ θ γ M A U e} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  interpret W γ θ M n ≢ failed U e
interpret-never-fails n W⊢ runtime runtime-env γ⊢ image M⊢ =
  outcome-typing-excludes-error
    (interpret-typing n W⊢ runtime runtime-env γ⊢ image M⊢)

empty-runtime-context :
  RuntimeContext emptyWorld zero [] []
empty-runtime-context =
  runtime-context length-empty []-scoped store-empty

closed-run-never-fails :
  ∀ n {M A U e} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  run M n ≢ failed U e
closed-run-never-fails n image M⊢ =
  interpret-never-fails n
    empty-world-typed empty-runtime-context
    runtime-type-empty environment-empty image M⊢
