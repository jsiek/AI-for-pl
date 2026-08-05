module proof.InterpreterIndexedForallProxyProof where

-- File Charter:
--   * Composes indexed forall-proxy instantiation in all three alignments.
--   * Charges constructor fuel only to endpoints that contain the proxy.
--   * Uses direct interpreter equations and unary terminal stability only.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
import Data.Nat

open import Interpreter
open import Core.InterpreterFuel using
  (coerceValue-terminal-stable; instantiateValue-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterForallProxyComputation using
  (forall-proxy-computation-eq)
open import proof.InterpreterIndexedOneSidedSequenceSimulation using
  (indexed-left-sequence-simulation)
open import proof.InterpreterIndexedRightSequenceSimulation using
  (indexed-right-sequence-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)

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
indexed-paired-forall-proxy-instantiation
    {W} {W′} {α} {α′} {θ} {θ′} {c} {c′} {V} {V′}
    head-simulation continuation-simulation =
  indexed-simulation-pointwise
    (λ n → forall-proxy-computation-eq
      {W = W} {α = α} {θ = θ} {c = c} {V = V} n)
    (λ n → forall-proxy-computation-eq
      {W = W′} {α = α′} {θ = θ′} {c = c′} {V = V′} n)
    (indexed-sequence-simulation
      head-simulation continuation-simulation
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = W} {α = α} {V = V} {n = n} {o = o}
          terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = W′} {α = α′} {V = V′} {n = n} {o = o}
          terminal eq k
        })
      (λ Z U {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z} {θ = seal-name α ∷ θ} {c = c} {V = U}
          {n = n} {o = o} terminal eq k)
      (λ Z′ U′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z′} {θ = seal-name α′ ∷ θ′}
          {c = c′} {V = U′} {n = n} {o = o}
          terminal eq k))

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
indexed-left-forall-proxy-instantiation
    {W} {W′} {α} {θ} {c} {V}
    head-simulation continuation-simulation =
  indexed-simulation-pointwise
    (λ n → forall-proxy-computation-eq
      {W = W} {α = α} {θ = θ} {c = c} {V = V} n)
    (λ n → refl)
    (indexed-left-sequence-simulation
      head-simulation continuation-simulation
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = W} {α = α} {V = V} {n = n} {o = o}
          terminal eq k
        })
      (λ Z U {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z} {θ = seal-name α ∷ θ} {c = c} {V = U}
          {n = n} {o = o} terminal eq k)
      refl)

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
indexed-right-forall-proxy-instantiation
    {W = W} {W′ = W′} {α′ = α′} {θ′ = θ′}
    {c′ = c′} {V′ = V′}
    head-simulation continuation-simulation =
  indexed-simulation-pointwise
    (λ n → refl)
    (λ n → forall-proxy-computation-eq
      {W = W′} {α = α′} {θ = θ′} {c = c′} {V = V′} n)
    (indexed-right-sequence-simulation
      head-simulation continuation-simulation refl
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = W′} {α = α′} {V = V′} {n = n} {o = o}
          terminal eq k
        })
      (λ Z′ U′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z′} {θ = seal-name α′ ∷ θ′}
          {c = c′} {V = U′} {n = n} {o = o}
          terminal eq k))
