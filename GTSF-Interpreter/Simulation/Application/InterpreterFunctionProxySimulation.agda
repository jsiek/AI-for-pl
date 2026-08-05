module Simulation.Application.InterpreterFunctionProxySimulation where

-- File Charter:
--   * Exposes direct paired simulation of semantic function-proxy application.
--   * States all three recursive phase simulations and error-freedom inputs.
--   * Delegates interpreter-equation composition to its private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterFunctionProxyTail using
  (function-proxy-tail)
import proof.InterpreterFunctionProxySimulationCases as Proof

open ITN.RelatedWorlds

paired-function-proxy-application :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  (domain-simulation :
    TerminalSimulation domain-result R
      (coerceValue W θ p U)
      (coerceValue W′ θ′ p′ U′)) →
  (application-simulation :
    ∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TerminalSimulation application-result S
      (applyValue Z V Q)
      (applyValue Z′ V′ Q′)) →
  (codomain-simulation :
    ∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TerminalSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′)) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    (R≤S : WorldExtension R S) →
    (Q~Q′ : domain-result S Q Q′) →
    ∀ {n T′ e} →
    function-proxy-tail θ′ q′ V′ Z′ Q′ n ≡
      failed T′ e →
    ⊥) →
  (∀ {n Z′ e} →
    applyValue W′ (function-proxy p′ q′ θ′ V′) U′ n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
paired-function-proxy-application =
  Proof.paired-function-proxy-application
