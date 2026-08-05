module proof.InterpreterIndexedFunctionProxyProof where

-- File Charter:
--   * Composes the three phases of indexed function-proxy application.
--   * Handles paired and one-sided proxies with explicit guarded identity
--     chains, charging constructor fuel only to the endpoint with a proxy.
--   * Contains no evaluator recursion or reduction semantics.

open import Agda.Builtin.Equality using (refl)
import Data.Nat
open import Relation.Binary.PropositionalEquality using (sym)

open import Interpreter
open import Core.InterpreterFuel using
  (applyValue-terminal-stable; coerceValue-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterFunctionProxyTail
open import proof.InterpreterIndexedChainSimulation using
  (indexed-chain-simulation)
open import proof.InterpreterIndexedGuardRemoval using
  (remove-left-guard; remove-right-guard)
open import proof.InterpreterIndexedImmediateChain using
  (immediate-sequence-computation-eq)
open import proof.InterpreterIndexedOneSidedSequenceSimulation using
  (indexed-left-chain-simulation)
open import proof.InterpreterIndexedRightSequenceSimulation using
  (indexed-right-chain-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-terminal-stable)

open ITN.RelatedWorlds
module WorldProperties = ITN.PersistentWorldProperties

indexed-function-proxy-tail :
  ∀ {W W′ θ θ′ q q′ V V′ U U′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (applyValue W V U)
    (applyValue W′ V′ U′) left-index right-index →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S P P′ →
    IndexedTerminalSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (function-proxy-tail θ q V W U)
    (function-proxy-tail θ′ q′ V′ W′ U′)
    left-index right-index
indexed-function-proxy-tail
    {W} {W′} {θ} {θ′} {q} {q′} {V} {V′} {U} {U′}
    head-simulation continuation-simulation =
  indexed-chain-simulation
    head-simulation continuation-simulation
    (λ { {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = W} {V = V} {U = U} {n = n} {o = o}
        terminal eq k
      })
    (λ { {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = W′} {V = V′} {U = U′} {n = n} {o = o}
        terminal eq k
      })
    (λ Z P {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = P}
        {n = n} {o = o} terminal eq k)
    (λ Z′ P′ {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z′} {θ = θ′} {c = q′} {V = P′}
        {n = n} {o = o} terminal eq k)

indexed-left-function-proxy-tail :
  ∀ {W W′ θ q V V′ U U′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (applyValue W V U)
    (applyValue W′ V′ U′) left-index right-index →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S P P′ →
    IndexedTerminalSimulation result S
      (coerceValue Z θ q P)
      (immediateReturn Z′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (function-proxy-tail θ q V W U)
    (applyValue W′ V′ U′) left-index right-index
indexed-left-function-proxy-tail
    {W} {W′} {θ} {q} {V} {V′} {U} {U′}
    head-simulation continuation-simulation =
  indexed-left-chain-simulation
    head-simulation continuation-simulation
    (λ { {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = W} {V = V} {U = U} {n = n} {o = o}
        terminal eq k
      })
    (λ Z P {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = P}
        {n = n} {o = o} terminal eq k)
    refl

indexed-right-function-proxy-tail :
  ∀ {W W′ θ′ q′ V V′ U U′ left-index right-index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  IndexedTerminalSimulation head-result R
    (applyValue W V U)
    (applyValue W′ V′ U′) left-index right-index →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S P P′ →
    IndexedTerminalSimulation result S
      (immediateReturn Z P)
      (coerceValue Z′ θ′ q′ P′) left-index right-index) →
  IndexedTerminalSimulation result R
    (applyValue W V U)
    (function-proxy-tail θ′ q′ V′ W′ U′)
    left-index right-index
indexed-right-function-proxy-tail
    {W} {W′} {θ′} {q′} {V} {V′} {U} {U′}
    head-simulation continuation-simulation =
  indexed-right-chain-simulation
    head-simulation continuation-simulation refl
    (λ { {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = W′} {V = V′} {U = U′} {n = n} {o = o}
        terminal eq k
      })
    (λ Z′ P′ {n} {o} terminal eq k →
      coerceValue-terminal-stable
        {W = Z′} {θ = θ′} {c = q′} {V = P′}
        {n = n} {o = o} terminal eq k)

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
indexed-paired-function-proxy-application
    {W} {W′} {θ} {θ′} {p} {p′} {q} {q′}
    {V} {V′} {U} {U′}
    domain-simulation application-simulation codomain-simulation =
  indexed-simulation-pointwise
    (λ n → function-proxy-computation-eq
      {W = W} {θ = θ} {p = p} {q = q}
      {V = V} {U = U} n)
    (λ n → function-proxy-computation-eq
      {W = W′} {θ = θ′} {p = p′} {q = q′}
      {V = V′} {U = U′} n)
    (indexed-sequence-simulation
      domain-simulation
      (λ R≤S Q~Q′ →
        indexed-function-proxy-tail
          (application-simulation R≤S Q~Q′)
          (λ S≤T P~P′ →
            codomain-simulation
              (ITN.PersistentWorldProperties.world-extension-trans R≤S S≤T)
              P~P′))
      (λ { {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = W} {θ = θ} {c = p} {V = U}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = W′} {θ = θ′} {c = p′} {V = U′}
          {n = n} {o = o} terminal eq k
        })
      (λ Z Q {n} {o} terminal eq k →
        function-proxy-tail-stable
          {W = Z} {θ = θ} {q = q} {V = V} {U = Q}
          {n = n} {o = o} terminal eq k)
      (λ Z′ Q′ {n} {o} terminal eq k →
        function-proxy-tail-stable
          {W = Z′} {θ = θ′} {q = q′} {V = V′} {U = Q′}
          {n = n} {o = o} terminal eq k))

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
indexed-left-function-proxy-application
    {W} {W′} {θ} {p} {q} {V} {V′} {U} {U′}
    domain-simulation application-simulation codomain-simulation =
  remove-right-guard
    (indexed-simulation-pointwise
      (λ n → function-proxy-computation-eq
        {W = W} {θ = θ} {p = p} {q = q}
        {V = V} {U = U} n)
      (λ n →
        sym
          (immediate-sequence-computation-eq
            {W = W′} {V = U′}
            {continuation = λ Z′ Q′ → applyValue Z′ V′ Q′}
            refl n))
      (indexed-sequence-simulation
        domain-simulation
        (λ R≤S Q~Q′ →
          indexed-left-function-proxy-tail
            (application-simulation R≤S Q~Q′)
            (λ S≤T P~P′ →
              codomain-simulation
                (WorldProperties.world-extension-trans R≤S S≤T)
                P~P′))
        (λ { {n} {o} terminal eq k →
          coerceValue-terminal-stable
            {W = W} {θ = θ} {c = p} {V = U}
            {n = n} {o = o} terminal eq k
          })
        (immediate-return-terminal-stable W′ U′)
        (λ Z Q {n} {o} terminal eq k →
          function-proxy-tail-stable
            {W = Z} {θ = θ} {q = q} {V = V} {U = Q}
            {n = n} {o = o} terminal eq k)
        (λ Z′ Q′ {n} {o} terminal eq k →
          applyValue-terminal-stable
            {W = Z′} {V = V′} {U = Q′}
            {n = n} {o = o} terminal eq k)))

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
indexed-right-function-proxy-application
    {W} {W′} {θ′} {p′} {q′} {V} {V′} {U} {U′}
    domain-simulation application-simulation codomain-simulation =
  remove-left-guard
    (indexed-simulation-pointwise
      (λ n →
        sym
          (immediate-sequence-computation-eq
            {W = W} {V = U}
            {continuation = λ Z Q → applyValue Z V Q}
            refl n))
      (λ n → function-proxy-computation-eq
        {W = W′} {θ = θ′} {p = p′} {q = q′}
        {V = V′} {U = U′} n)
      (indexed-sequence-simulation
        domain-simulation
        (λ R≤S Q~Q′ →
          indexed-right-function-proxy-tail
            (application-simulation R≤S Q~Q′)
            (λ S≤T P~P′ →
              codomain-simulation
                (WorldProperties.world-extension-trans R≤S S≤T)
                P~P′))
        (immediate-return-terminal-stable W U)
        (λ { {n} {o} terminal eq k →
          coerceValue-terminal-stable
            {W = W′} {θ = θ′} {c = p′} {V = U′}
            {n = n} {o = o} terminal eq k
          })
        (λ Z Q {n} {o} terminal eq k →
          applyValue-terminal-stable
            {W = Z} {V = V} {U = Q}
            {n = n} {o = o} terminal eq k)
        (λ Z′ Q′ {n} {o} terminal eq k →
          function-proxy-tail-stable
            {W = Z′} {θ = θ′} {q = q′} {V = V′} {U = Q′}
            {n = n} {o = o} terminal eq k)))
