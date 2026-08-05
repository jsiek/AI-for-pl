module Runtime.InterpreterInertFrameCore where

-- File Charter:
--   * Defines the result of executing one inert coercion on a runtime value.
--   * Records the concrete wrapper, its explicit frame, and its positive-fuel
--     interpreter equation.
--   * Contains no proof implementation and imports no reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
open import Data.Nat using (suc)

open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Types

record InertFrameExecution
    (W : World) (θ : TypeEnvironment)
    (c : Coercion) (V : Value)
    (inert : Inert c) : Set where
  constructor inert-frame-execution
  field
    result : Value
    frame : ClosedValueFrame θ V inert result
    computes :
      ∀ n →
      coerceValue W θ c V (suc n) ≡ returned W result

open InertFrameExecution public
