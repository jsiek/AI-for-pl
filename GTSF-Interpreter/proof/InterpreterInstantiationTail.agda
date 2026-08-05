module proof.InterpreterInstantiationTail where

-- File Charter:
--   * Defines the direct computation after a polymorphic operand returns.
--   * Makes allocation, semantic instantiation, and the reveal coercion
--     explicit and proves the whole term equation and terminal stability.
--   * Contains no term narrowing or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)

import Coercions
open import Interpreter
open import Core.InterpreterFuel using
  (coerceValue-terminal-stable; instantiateValue-terminal-stable)
open import Simulation.Core.InterpreterSimulationResult
import NuTerms as N
open import proof.InterpreterSimulationHelpers using
  (chain-terminal-stable)
import Types

instantiation-coercion-continuation :
  SealName →
  TypeEnvironment →
  Coercions.Coercion →
  World →
  Value →
  Computation
instantiation-coercion-continuation α θ c W V =
  coerceValue W (seal-name α ∷ θ) c V

instantiation-tail :
  World →
  TypeEnvironment →
  Types.Ty →
  Coercions.Coercion →
  Value →
  Computation
instantiation-tail W θ A c V =
  chain
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (instantiation-coercion-continuation
      (freshSealName W) θ c)

instantiation-computation-eq :
  ∀ {W γ θ A L c} n →
  interpret W γ θ (N.ν A L c) n ≡
  sequence W
    (interpret W γ θ L)
    (λ U V → instantiation-tail U θ A c V)
    n
instantiation-computation-eq zero =
  refl
instantiation-computation-eq
    {W} {γ} {θ} {A} {L} {c} (suc n)
    with interpret W γ θ L n
instantiation-computation-eq (suc n) | timed U =
  refl
instantiation-computation-eq (suc n) | blamed U =
  refl
instantiation-computation-eq (suc n) | failed U e =
  refl
instantiation-computation-eq
    {W} {γ} {θ} {A} {L} {c} (suc n)
    | returned U V
    with instantiateValue
      (allocate U A θ) (freshSealName U) V n
instantiation-computation-eq (suc n)
    | returned U V | timed Z =
  refl
instantiation-computation-eq (suc n)
    | returned U V | blamed Z =
  refl
instantiation-computation-eq (suc n)
    | returned U V | failed Z e =
  refl
instantiation-computation-eq (suc n)
    | returned U V | returned Z Q =
  refl

instantiation-tail-stable :
  ∀ {W θ A c V} →
  TerminalStable (instantiation-tail W θ A c V)
instantiation-tail-stable
    {W} {θ} {A} {c} {V}
    {n = n} {o = o} terminal eq k =
  chain-terminal-stable
    {head =
      instantiateValue
        (allocate W A θ) (freshSealName W) V}
    {continuation =
      instantiation-coercion-continuation
        (freshSealName W) θ c}
    (λ { {n} {o} terminal eq k →
      instantiateValue-terminal-stable
        {W = allocate W A θ}
        {α = freshSealName W} {V = V}
        {n = n} {o = o} terminal eq k
      })
    (λ U Q {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = U} {θ = seal-name (freshSealName W) ∷ θ}
        {c = c} {V = Q}
        {n = n} {o = o} terminal eq k)
    {n = n} {o = o} terminal eq k
