module Simulation.Polymorphism.InterpreterRightForallProxySimulation where

-- File Charter:
--   * Exposes target-only simulation of forall-proxy instantiation.
--   * States target payload-instantiation and stored-coercion simulations.
--   * Keeps unary target error freedom explicit.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterRightForallProxySimulationCases as Proof

open ITN.RelatedWorlds

right-forall-proxy-instantiation :
  ∀ {W W′ α′ θ′ c′ V V′}
    {instantiation-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (instantiation-simulation :
    TerminalSimulation instantiation-result R
      (immediateReturn W V)
      (instantiateValue W′ α′ V′)) →
  (coercion-simulation :
    ∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    instantiation-result S U U′ →
    TerminalSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)) →
  (∀ {n Z′ e} →
    instantiateValue W′ α′ (forall-proxy c′ θ′ V′) n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
right-forall-proxy-instantiation =
  Proof.right-forall-proxy-instantiation
