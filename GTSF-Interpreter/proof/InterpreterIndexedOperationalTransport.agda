module proof.InterpreterIndexedOperationalTransport where

-- File Charter:
--   * Transports indexed operational simulations across semantic-type
--     equalities.
--   * Changes only the returned-value relation; computations and indices
--     remain untouched.
--   * Contains no recursive driver or reduction semantics.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (SemanticType)
open import Simulation.Core.InterpreterSimulationResult using (Computation)
open import Narrowing.InterpreterTermNarrowing
open import proof.InterpreterIndexedResultMap using
  (indexed-result-map)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-operational-result-transport :
  ∀ {W W′ A A′ B B′ left-index right-index}
    {R : WorldRelation W W′}
    {left right : Computation} →
  A ≡ A′ →
  B ≡ B′ →
  IndexedTerminalSimulation
    (OperationalValueResult A B) R left right
    left-index right-index →
  IndexedTerminalSimulation
    (OperationalValueResult A′ B′) R left right
    left-index right-index
indexed-operational-result-transport left-eq right-eq simulation =
  indexed-result-map simulation
    (λ R≤S value →
      operational-value-type-transport left-eq right-eq value)
