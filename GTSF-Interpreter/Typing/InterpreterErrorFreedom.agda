module Typing.InterpreterErrorFreedom where

-- File Charter:
--   * EXPERIMENTAL compiled-endpoint facade: its general unary theorems are
--     live, but the two compiler corollaries await the O35 QTI migration.
--   * Public error-freedom theorem for the direct fuel-indexed interpreter.
--   * Distinguishes interpreter implementation errors from semantic blame.
--   * Exposes both the general semantic-typing theorem and its closed-run
--     corollary without using reduction.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Compile using (compileᵀ)
open import Ctx using (ctxWf-[])
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Typing.InterpreterSemanticTyping
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
import NuTerms as N
import proof.InterpreterErrorFreedomCore as Core
import proof.InterpreterErrorFreedomProof as CompiledProof
import proof.InterpreterTypingCore as Typing
open import Types

outcome-typing-excludes-error :
  ∀ {W A o U e} →
  OutcomeTyping W A o →
  o ≢ failed U e
outcome-typing-excludes-error =
  Core.outcome-typing-excludes-error

interpret-preserves-semantic-typing :
  ∀ n {W Δ Σ Γ θ γ M A} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  OutcomeTyping W ⟦ A ⟧[ θ ]
    (interpret W γ θ M n)
interpret-preserves-semantic-typing =
  Typing.interpret-typing

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
  Core.interpret-never-fails n W⊢ runtime runtime-env γ⊢ image M⊢

empty-runtime-context :
  RuntimeContext emptyWorld zero [] []
empty-runtime-context =
  Core.empty-runtime-context

closed-run-never-fails :
  ∀ n {M A U e} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  run M n ≢ failed U e
closed-run-never-fails n image M⊢ =
  Core.closed-run-never-fails n image M⊢

compiled-source-never-fails :
  ∀ {M M′ A B}
    {p : [] ∣ zero ⊢ A ⊑ B ⊣ zero} →
  (M⊑M′ : [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n U e →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    N = proj₁ (compileᵀ ctxWf-[] M⊢)
  in
  run N n ≢ failed U e
compiled-source-never-fails =
  CompiledProof.compiled-source-never-fails

compiled-target-never-fails :
  ∀ {M M′ A B}
    {p : [] ∣ zero ⊢ A ⊑ B ⊣ zero} →
  (M⊑M′ : [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n U e →
  let
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N′ = proj₁ (compileᵀ ctxWf-[] M′⊢)
  in
  run N′ n ≢ failed U e
compiled-target-never-fails =
  CompiledProof.compiled-target-never-fails
