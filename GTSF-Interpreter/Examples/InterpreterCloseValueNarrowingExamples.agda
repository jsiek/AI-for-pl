module Examples.InterpreterCloseValueNarrowingExamples where

-- File Charter:
--   * Regression-checks the public close-value fundamental theorem.
--   * Uses the closed constant case to exercise the empty runtime boundary.
--   * Contains no evaluation or reduction argument.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat using (z≤n)

open import Interpreter
open import Narrowing.InterpreterCloseValueNarrowing
open import ImprecisionWf using (idι)
open import Typing.InterpreterSemanticTypingCore using (environment-empty)
open import Simulation.Core.InterpreterSimulationContext using
  (empty-runtime-narrowing; runtime-narrowing-frame)
open import SmallStepInterface.InterpreterTermAlignment using (constant-aligned)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import NuTerms as N
open import Primitives using (κℕ)
open import Types using (`ℕ; ‵_)

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

constant-terms :
  OpenInterpreterTermNarrowing
    empty-world⊑ [] 0 0 [] []
    (N.$ (κℕ 7)) (N.$ (κℕ 7))
    (‵ `ℕ) (‵ `ℕ) idι
constant-terms =
  open-interpreter-narrowing constant-aligned

constant-close-narrows :
  ValueNarrowing empty-world⊑
    (constant (κℕ 7))
    (constant (κℕ 7))
constant-close-narrows =
  closeValue-preserves-narrowing
    constant-terms
    (runtime-narrowing-frame empty-runtime-narrowing)
    environment-empty
    environment-empty
    empty-type-environment-realization
    []⊑[]ᵉ
    z≤n
    (N.$ (κℕ 7))
    (N.$ (κℕ 7))
    refl
    refl
