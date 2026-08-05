module Simulation.Indexed.InterpreterIndexedGeneralizedValue where

-- File Charter:
--   * Exposes fuel-indexed paired and one-sided generalized instantiation.
--   * Charges the generalized-value constructor guard explicitly.
--   * Delegates direct computation transport to `proof/`.

open import Data.List using (_∷_)
import Data.Nat

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterIndexedGeneralizedValueProof as Proof

open ITN.RelatedWorlds

indexed-paired-generalized-instantiation :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′
      left-index right-index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    left-index right-index →
  IndexedTerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-paired-generalized-instantiation =
  Proof.indexed-paired-generalized-instantiation

indexed-left-generalized-instantiation :
  ∀ {W W′ α A c θ V V′ left-index right-index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) left-index right-index →
  IndexedTerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′)
    (Data.Nat.suc left-index)
    right-index
indexed-left-generalized-instantiation =
  Proof.indexed-left-generalized-instantiation

indexed-right-generalized-instantiation :
  ∀ {W W′ α′ A′ c′ θ′ V V′ left-index right-index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    left-index right-index →
  IndexedTerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    left-index
    (Data.Nat.suc right-index)
indexed-right-generalized-instantiation =
  Proof.indexed-right-generalized-instantiation
