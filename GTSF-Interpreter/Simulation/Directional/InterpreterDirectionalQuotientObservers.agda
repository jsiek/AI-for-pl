module Simulation.Directional.InterpreterDirectionalQuotientObservers where

-- File Charter:
--   * Packages the active quotient down/up observations consumed together by
--     one layer of the mutual fuel induction.
--   * Keeps each terminal direction explicit instead of hiding it behind a
--     polymorphic direction argument.
--   * Contains no recursion, interpreter equation, or small-step result.

open import Data.Nat using (zero)

open import Interpreter using (StepIndex)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Coercion.InterpreterOperationalQuotientSimulationMotive
import proof.InterpreterDirectionalZero as Zero

record DirectionalQuotientExecutionObservers
    (index : StepIndex) : Set₂ where
  constructor quotient-execution-observers
  field
    down-forward :
      DirectionalQuotientDownSimulation forward-direction index
    down-backward :
      DirectionalQuotientDownSimulation backward-direction index
    down-target-blame :
      DirectionalQuotientDownSimulation target-blame-direction index
    up-forward :
      DirectionalQuotientUpSimulation forward-direction index
    up-backward :
      DirectionalQuotientUpSimulation backward-direction index
    up-target-blame :
      DirectionalQuotientUpSimulation target-blame-direction index

open DirectionalQuotientExecutionObservers public

zero-quotient-execution-observers :
  DirectionalQuotientExecutionObservers zero
zero-quotient-execution-observers =
  quotient-execution-observers
    Zero.quotient-down-forward-zero
    Zero.quotient-down-backward-zero
    Zero.quotient-down-target-blame-zero
    Zero.quotient-up-forward-zero
    Zero.quotient-up-backward-zero
    Zero.quotient-up-target-blame-zero
