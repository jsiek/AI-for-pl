module Simulation.Polymorphism.InterpreterRightGeneralizedValueSimulation where

-- File Charter:
--   * Exposes target-only simulation of generalized-value instantiation.
--   * States the stored-coercion simulation while the source stays returned.
--   * Delegates one-sided constructor-fuel transport to its proof module.

open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterRightGeneralizedValueSimulationCases as Proof

open ITN.RelatedWorlds

right-generalized-value-instantiation :
  ∀ {W W′ α′ A′ c′ θ′ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′) →
  TerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
right-generalized-value-instantiation =
  Proof.right-generalized-value-instantiation
