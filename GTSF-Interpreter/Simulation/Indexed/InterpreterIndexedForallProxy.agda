module Simulation.Indexed.InterpreterIndexedForallProxy where

-- File Charter:
--   * Exposes fuel-indexed paired and one-sided forall-proxy instantiation.
--   * Takes wrapped-instantiation and stored-coercion simulations explicitly.
--   * Delegates direct interpreter-equation composition to `proof/`.

open import Data.List using (_∷_)
import Data.Nat

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterIndexedForallProxyProof as Proof

open ITN.RelatedWorlds

indexed-paired-forall-proxy-instantiation :
  ∀ {W W′ α α′ θ θ′ c c′ V V′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) left-index right-index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    IndexedTerminalSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      left-index right-index) →
  IndexedTerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-paired-forall-proxy-instantiation =
  Proof.indexed-paired-forall-proxy-instantiation

indexed-left-forall-proxy-instantiation :
  ∀ {W W′ α θ c V V′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (instantiateValue W α V)
    (immediateReturn W′ V′) left-index right-index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    IndexedTerminalSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) left-index right-index) →
  IndexedTerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′)
    (Data.Nat.suc left-index)
    right-index
indexed-left-forall-proxy-instantiation =
  Proof.indexed-left-forall-proxy-instantiation

indexed-right-forall-proxy-instantiation :
  ∀ {W W′ α′ θ′ c′ V V′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) left-index right-index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    IndexedTerminalSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      left-index right-index) →
  IndexedTerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    left-index
    (Data.Nat.suc right-index)
indexed-right-forall-proxy-instantiation =
  Proof.indexed-right-forall-proxy-instantiation
