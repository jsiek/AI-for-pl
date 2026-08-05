module proof.InterpreterDirectionalPositiveIndexed where

-- File Charter:
--   * Projects paired and one-sided positive indexed simulations to any one
--     of the three directional observations used by the fuel driver.
--   * Centralizes the asymmetric successor placement for one-sided actions.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Data.Nat using (suc; zero)

open import Interpreter using (World)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult using
  (Computation; ValueResultRelation)
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds


paired-positive-direction :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (direction : TerminalDirection) →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) (suc right-index)) →
  DirectionalObservation direction value-result R left right
    (suc index)
paired-positive-direction
    {index = index} forward-direction simulation =
  forward-return (simulation index zero)
paired-positive-direction
    {index = index} backward-direction simulation =
  backward-return (simulation zero index)
paired-positive-direction
    {index = index} target-blame-direction simulation =
  target-blame-reflects (simulation zero index)


left-positive-direction :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (direction : TerminalDirection) →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) right-index) →
  DirectionalObservation direction value-result R left right
    (suc index)
left-positive-direction
    {index = index} forward-direction simulation =
  forward-return (simulation index zero)
left-positive-direction
    {index = index} backward-direction simulation =
  backward-return (simulation zero (suc index))
left-positive-direction
    {index = index} target-blame-direction simulation =
  target-blame-reflects (simulation zero (suc index))


right-positive-direction :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (direction : TerminalDirection) →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index (suc right-index)) →
  DirectionalObservation direction value-result R left right
    (suc index)
right-positive-direction
    {index = index} forward-direction simulation =
  forward-return (simulation (suc index) zero)
right-positive-direction
    {index = index} backward-direction simulation =
  backward-return (simulation zero index)
right-positive-direction
    {index = index} target-blame-direction simulation =
  target-blame-reflects (simulation zero index)
