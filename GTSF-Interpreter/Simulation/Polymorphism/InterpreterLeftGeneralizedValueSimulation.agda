module Simulation.Polymorphism.InterpreterLeftGeneralizedValueSimulation where

-- File Charter:
--   * Exposes source-only simulation of generalized-value instantiation.
--   * States the stored-coercion simulation while the target stays returned.
--   * Delegates one-sided constructor-fuel transport to its proof module.

open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterLeftGeneralizedValueSimulationCases as Proof

open ITN.RelatedWorlds

left-generalized-value-instantiation :
  ∀ {W W′ α A c θ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) →
  TerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′)
left-generalized-value-instantiation =
  Proof.left-generalized-value-instantiation
