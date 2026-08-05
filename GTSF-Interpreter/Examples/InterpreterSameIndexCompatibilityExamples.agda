module Examples.InterpreterSameIndexCompatibilityExamples where

-- File Charter:
--   * Checks the same-index compatibility theorem on an interpreted identity.
--   * Produces the concrete existential joined-value certificate.
--   * Contains no catch-up procedure or reduction semantics.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)

open import Coercions renaming (id to idᶜ)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionConstructorSimulation
open import Simulation.Core.InterpreterSameIndexCompatibility
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Primitives using (κℕ)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

Nat : Ty
Nat =
  ‵ `ℕ

seven : Value
seven =
  constant (κℕ 7)

identity-simulation :
  TerminalSimulation ValueNarrowing empty-world⊑
    (coerceValue emptyWorld [] (idᶜ Nat) seven)
    (coerceValue emptyWorld [] (idᶜ Nat) seven)
identity-simulation =
  paired-id-coercion-simulation
    (constant⊑ (κℕ 7))

same-index-identity-joined :
  JoinedValues.Joined emptyWorld seven emptyWorld seven
same-index-identity-joined =
  same-index-returned-joined
    identity-simulation
    {n = suc zero}
    refl refl
