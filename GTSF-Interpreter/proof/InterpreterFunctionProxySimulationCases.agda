module proof.InterpreterFunctionProxySimulationCases where

-- File Charter:
--   * Composes domain coercion, underlying application, and codomain coercion.
--   * Allows every phase to converge at an independently chosen fuel index.
--   * Uses direct interpreter equations and unary target error freedom only.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

open import Interpreter
open import Core.InterpreterFuel using (coerceValue-terminal-stable)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterTermNarrowing as ITN
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import proof.InterpreterFunctionProxyTail
open import proof.InterpreterSequenceSimulation using
  (chain-simulation; sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

module ProxyWorldProperties =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

function-proxy-tail-simulation :
  ∀ {W W′ θ θ′ q q′ V V′ U U′}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (head-simulation :
    TerminalSimulation head-result R
      (applyValue W V U)
      (applyValue W′ V′ U′)) →
  (continuation-simulation :
    ∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S Q Q′ →
    TerminalSimulation result S
      (coerceValue Z θ q Q)
      (coerceValue Z′ θ′ q′ Q′)) →
  (∀ {n Z′ e} →
    function-proxy-tail θ′ q′ V′ W′ U′ n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (function-proxy-tail θ q V W U)
    (function-proxy-tail θ′ q′ V′ W′ U′)
function-proxy-tail-simulation
    {W} {W′} {θ} {θ′} {q} {q′} {V} {V′} {U} {U′}
    {R = R}
    head-simulation continuation-simulation
    right-error-free =
  chain-simulation
    {W = W} {W′ = W′} {R = R}
    {left-head = applyValue W V U}
    {right-head = applyValue W′ V′ U′}
    {left-continuation = function-proxy-continuation θ q}
    {right-continuation = function-proxy-continuation θ′ q′}
    head-simulation
    continuation-simulation
    (λ Z Q {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = Q}
        {n = n} {o = o} terminal eq k)
    (λ Z′ Q′ {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z′} {θ = θ′} {c = q′} {V = Q′}
        {n = n} {o = o} terminal eq k)
    (λ { {n} {Z′} {e} eq →
      right-error-free {n = n} {Z′ = Z′} {e = e} eq
      })

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
paired-function-proxy-application
    {W} {W′} {θ} {θ′} {p} {p′} {q} {q′}
    {V} {V′} {U} {U′} {R = R}
    domain-simulation application-simulation
    codomain-simulation right-tail-error-free
    right-application-error-free =
  simulation-pointwise
    (λ n →
      function-proxy-computation-eq
        {W = W} {θ = θ} {p = p} {q = q}
        {V = V} {U = U} n)
    (λ n →
      function-proxy-computation-eq
        {W = W′} {θ = θ′} {p = p′} {q = q′}
        {V = V′} {U = U′} n)
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = coerceValue W θ p U}
      {right-head = coerceValue W′ θ′ p′ U′}
      {left-continuation =
        λ Z Q → function-proxy-tail θ q V Z Q}
      {right-continuation =
        λ Z′ Q′ → function-proxy-tail θ′ q′ V′ Z′ Q′}
      domain-simulation
      (λ R≤S Q~Q′ →
        function-proxy-tail-simulation
          (application-simulation R≤S Q~Q′)
          (λ S≤T P~P′ →
            codomain-simulation
              (ProxyWorldProperties.world-extension-trans R≤S S≤T)
              P~P′)
          (λ { {n} {Z′} {e} eq →
            right-tail-error-free R≤S Q~Q′
              {n = n} {T′ = Z′} {e = e} eq
            }))
      (λ Z Q {n} {o} terminal eq k →
        function-proxy-tail-stable
          {W = Z} {θ = θ} {q = q} {V = V} {U = Q}
          {n = n} {o = o} terminal eq k)
      (λ Z′ Q′ {n} {o} terminal eq k →
        function-proxy-tail-stable
          {W = Z′} {θ = θ′} {q = q′} {V = V′} {U = Q′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} {Z′} {e} eq →
        right-application-error-free
          {n = n} {Z′ = Z′} {e = e}
          (trans
            (function-proxy-computation-eq
              {W = W′} {θ = θ′} {p = p′} {q = q′}
              {V = V′} {U = U′} n)
            eq)
        }))
