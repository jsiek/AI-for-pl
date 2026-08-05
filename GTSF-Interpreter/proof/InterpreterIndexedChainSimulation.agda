module proof.InterpreterIndexedChainSimulation where

-- File Charter:
--   * Composes fuel-local simulations through unguarded interpreter chaining.
--   * Reuses the checked indexed sequence algebra and removes its two outer
--     guards constructively.
--   * Contains no evaluator recursion or reduction semantics.

open import Interpreter using (Value; World)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterIndexedGuardRemoval using
  (remove-both-guards)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)

open ITN.InterpreterValues
open ITN.RelatedWorlds

indexed-chain-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index right-index) →
  TerminalStable left-head →
  TerminalStable right-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  IndexedTerminalSimulation continuation-result R
    (chain left-head left-continuation)
    (chain right-head right-continuation)
    left-index right-index
indexed-chain-simulation
    head-simulation continuation-simulation
    left-head-stable right-head-stable
    left-continuation-stable right-continuation-stable =
  remove-both-guards
    (indexed-sequence-simulation
      head-simulation continuation-simulation
      left-head-stable right-head-stable
      left-continuation-stable right-continuation-stable)
