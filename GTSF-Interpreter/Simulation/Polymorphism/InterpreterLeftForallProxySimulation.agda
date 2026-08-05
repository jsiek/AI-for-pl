module Simulation.Polymorphism.InterpreterLeftForallProxySimulation where

-- File Charter:
--   * Exposes source-only simulation of forall-proxy instantiation.
--   * States the recursive wrapped-value and stored-coercion simulations.
--   * Keeps the target at its already returned value throughout catch-up.

open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterLeftForallProxySimulationCases as Proof

open ITN.RelatedWorlds

left-forall-proxy-instantiation :
  ∀ {W W′ α θ c V V′}
    {instantiation-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (instantiation-simulation :
    TerminalSimulation instantiation-result R
      (instantiateValue W α V)
      (immediateReturn W′ V′)) →
  (coercion-simulation :
    ∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    instantiation-result S U U′ →
    TerminalSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′)) →
  TerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′)
left-forall-proxy-instantiation =
  Proof.left-forall-proxy-instantiation
