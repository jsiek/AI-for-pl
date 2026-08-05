module Simulation.Indexed.InterpreterIndexedFunctionProxy where

-- File Charter:
--   * Exposes indexed semantic application through paired and one-sided
--     function proxies.
--   * Takes domain-cast, wrapped-application, and codomain-cast simulations
--     explicitly.
--   * Delegates direct interpreter-equation composition to `proof/`.

import Data.Nat
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterIndexedFunctionProxyProof as Proof

open ITN.RelatedWorlds

indexed-paired-function-proxy-application :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′ left-index right-index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation domain-result R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) left-index right-index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    IndexedTerminalSimulation application-result S
      (applyValue Z V Q)
      (applyValue Z′ V′ Q′) left-index right-index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    IndexedTerminalSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-paired-function-proxy-application =
  Proof.indexed-paired-function-proxy-application

indexed-left-function-proxy-application :
  ∀ {W W′ θ p q V V′ U U′ left-index right-index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation domain-result R
    (coerceValue W θ p U)
    (immediateReturn W′ U′) left-index right-index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    IndexedTerminalSimulation application-result S
      (applyValue Z V Q)
      (applyValue Z′ V′ Q′) left-index right-index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    IndexedTerminalSimulation result S
      (coerceValue Z θ q P)
      (immediateReturn Z′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ V′ U′)
    (Data.Nat.suc left-index)
    right-index
indexed-left-function-proxy-application =
  Proof.indexed-left-function-proxy-application

indexed-right-function-proxy-application :
  ∀ {W W′ θ′ p′ q′ V V′ U U′ left-index right-index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation domain-result R
    (immediateReturn W U)
    (coerceValue W′ θ′ p′ U′) left-index right-index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    IndexedTerminalSimulation application-result S
      (applyValue Z V Q)
      (applyValue Z′ V′ Q′) left-index right-index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    IndexedTerminalSimulation result S
      (immediateReturn Z P)
      (coerceValue Z′ θ′ q′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (applyValue W V U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    left-index
    (Data.Nat.suc right-index)
indexed-right-function-proxy-application =
  Proof.indexed-right-function-proxy-application
