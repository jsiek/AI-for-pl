module Simulation.Indexed.InterpreterIndexedPrimitive where

-- File Charter:
--   * Exposes positive-index composition for compiler-aligned primitive
--     terms.
--   * Takes both recursive operand simulations explicitly.
--   * Delegates the reduction-free sequencing proof to a private module.

open import ImprecisionWf using (idι)
import Data.Nat
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (base-type)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (addℕ)
import proof.InterpreterIndexedPrimitiveProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-primitive-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M)
    (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  IndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  IndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  IndexedTerminalSimulation
    (OperationalValueResult
      (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-primitive-suc-simulation =
  Proof.indexed-primitive-suc-simulation
