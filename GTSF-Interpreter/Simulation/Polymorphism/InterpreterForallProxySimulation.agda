module Simulation.Polymorphism.InterpreterForallProxySimulation where

-- File Charter:
--   * Exposes direct paired simulation of forall-proxy instantiation.
--   * States the underlying-instantiation and stored-coercion simulations.
--   * Delegates interpreter-equation composition to its private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterForallProxySimulationCases as Proof

open ITN.RelatedWorlds

paired-forall-proxy-instantiation :
  ∀ {W W′ α α′ θ θ′ c c′ V V′}
    {instantiation-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (instantiation-simulation :
    TerminalSimulation instantiation-result R
      (instantiateValue W α V)
      (instantiateValue W′ α′ V′)) →
  (coercion-simulation :
    ∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    instantiation-result S U U′ →
    TerminalSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)) →
  (∀ {n Z′ e} →
    instantiateValue W′ α′ (forall-proxy c′ θ′ V′) n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
paired-forall-proxy-instantiation =
  Proof.paired-forall-proxy-instantiation
