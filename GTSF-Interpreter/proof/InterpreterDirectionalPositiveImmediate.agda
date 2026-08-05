module proof.InterpreterDirectionalPositiveImmediate where

-- File Charter:
--   * Projects positive-fuel indexed simulations to the three directional
--     observations used by the mutual interpreter driver.
--   * Covers paired, source-only, and target-only immediate constructors.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Data.Nat using (suc; zero)

open import Interpreter using (World)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult using
  (Computation; ValueResultRelation)
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds


paired-positive-forward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) (suc right-index)) →
  ForwardReturnSimulation value-result R left right (suc index)
paired-positive-forward {index = index} simulation =
  forward-return (simulation index zero)


paired-positive-backward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) (suc right-index)) →
  BackwardReturnSimulation value-result R left right (suc index)
paired-positive-backward {index = index} simulation =
  backward-return (simulation zero index)


paired-positive-target-blame :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) (suc right-index)) →
  TargetBlameSimulation R left right (suc index)
paired-positive-target-blame {index = index} simulation =
  target-blame-reflects (simulation zero index)


left-positive-forward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) right-index) →
  ForwardReturnSimulation value-result R left right (suc index)
left-positive-forward {index = index} simulation =
  forward-return (simulation index zero)


left-positive-backward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) right-index) →
  BackwardReturnSimulation value-result R left right (suc index)
left-positive-backward {index = index} simulation =
  backward-return (simulation zero (suc index))


left-positive-target-blame :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      (suc left-index) right-index) →
  TargetBlameSimulation R left right (suc index)
left-positive-target-blame {index = index} simulation =
  target-blame-reflects (simulation zero (suc index))


right-positive-forward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index (suc right-index)) →
  ForwardReturnSimulation value-result R left right (suc index)
right-positive-forward {index = index} simulation =
  forward-return (simulation (suc index) zero)


right-positive-backward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index (suc right-index)) →
  BackwardReturnSimulation value-result R left right (suc index)
right-positive-backward {index = index} simulation =
  backward-return (simulation zero index)


right-positive-target-blame :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index (suc right-index)) →
  TargetBlameSimulation R left right (suc index)
right-positive-target-blame {index = index} simulation =
  target-blame-reflects (simulation zero index)
