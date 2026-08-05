module Simulation.Polymorphism.InterpreterGeneralizedValueSimulation where

-- File Charter:
--   * Exposes direct paired simulation of generalized-value instantiation.
--   * States the stored-coercion simulation with distinct nominal names.
--   * Delegates fuel-guard transport to its private proof module.

open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterGeneralizedValueSimulationCases as Proof

open ITN.RelatedWorlds

paired-generalized-value-instantiation :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′) →
  TerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
paired-generalized-value-instantiation =
  Proof.paired-generalized-value-instantiation
