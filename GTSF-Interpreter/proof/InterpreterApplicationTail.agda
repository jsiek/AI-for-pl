module proof.InterpreterApplicationTail where

-- File Charter:
--   * Defines the direct interpreter computation after a function returns.
--   * Proves the application equation, terminal stability, and typed target
--     error exclusion for argument evaluation followed by `applyValue`.
--   * Contains no term-narrowing or reduction argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Core.InterpreterFuel using
  (applyValue-terminal-stable; interpret-terminal-stable)
open import Core.InterpreterOutcome
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationResult
import NuTerms as N
open import proof.InterpreterSimulationHelpers using
  (chain-terminal-stable)
import proof.InterpreterTypingCore as Typing

application-continuation :
  Value →
  World →
  Value →
  Computation
application-continuation V W U =
  applyValue W V U

application-tail :
  World →
  Environment →
  TypeEnvironment →
  N.Term →
  Value →
  Computation
application-tail W γ θ M V =
  chain (interpret W γ θ M) (application-continuation V)

application-computation-eq :
  ∀ {W γ θ L M} n →
  interpret W γ θ (L N.· M) n ≡
  sequence W
    (interpret W γ θ L)
    (λ U V → application-tail U γ θ M V)
    n
application-computation-eq zero =
  refl
application-computation-eq {W} {γ} {θ} {L} {M} (suc n)
    with interpret W γ θ L n
application-computation-eq (suc n) | timed U =
  refl
application-computation-eq (suc n) | blamed U =
  refl
application-computation-eq (suc n) | failed U e =
  refl
application-computation-eq
    {W} {γ} {θ} {L} {M} (suc n) | returned U V
    with interpret U γ θ M n
application-computation-eq (suc n)
    | returned U V | timed Z =
  refl
application-computation-eq (suc n)
    | returned U V | blamed Z =
  refl
application-computation-eq (suc n)
    | returned U V | failed Z e =
  refl
application-computation-eq (suc n)
    | returned U V | returned Z Q =
  refl

application-tail-error-impossible :
  ∀ {W γ θ M V A B} →
  ValueTyping W V (A ⇒ᵛ B) →
  (∀ n → OutcomeTyping W A (interpret W γ θ M n)) →
  ∀ {n Z e} →
  application-tail W γ θ M V n ≡ failed Z e →
  ⊥
application-tail-error-impossible
    {W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    with interpret W γ θ M n in head-eq
application-tail-error-impossible
    {W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    | timed U =
  timed≢failed result-eq
application-tail-error-impossible
    {W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    | blamed U =
  blamed≢failed result-eq
application-tail-error-impossible
    {W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    | failed U e =
  outcome-typing-excludes-error (M-typing n) head-eq
application-tail-error-impossible
    {W = W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    | returned U Q
    with subst (OutcomeTyping W _) head-eq (M-typing n)
application-tail-error-impossible
    {W = W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    | returned U Q | return-typed W≤U U⊢ Q⊢ =
  outcome-typing-excludes-error
    (Typing.applyValue-typing n U⊢
      (semantic-value-world-weaken W≤U U⊢ V⊢)
      Q⊢)
    result-eq

application-tail-stable :
  ∀ {W γ θ M V} →
  TerminalStable (application-tail W γ θ M V)
application-tail-stable
    {W} {γ} {θ} {M} {V}
    {n = n} {o = o} terminal eq k =
  chain-terminal-stable
    {head = interpret W γ θ M}
    {continuation = application-continuation V}
    (λ { {n} {o} terminal eq k →
      interpret-terminal-stable
        {W = W} {γ = γ} {θ = θ} {M = M}
        {n = n} {o = o} terminal eq k
      })
    (λ U Q {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = U} {V = V} {U = Q}
        {n = n} {o = o} terminal eq k)
    {n = n} {o = o} terminal eq k
