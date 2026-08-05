module proof.InterpreterIndexedGeneralizedValueProof where

-- File Charter:
--   * Transports indexed coercion simulations through generalized values.
--   * Covers paired, source-only, and target-only constructor guards.
--   * Contains no evaluator recursion or reduction semantics.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
import Data.Nat

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterGeneralizedValueComputation using
  (generalized-value-computation-eq)
open import proof.InterpreterIndexedGuardSimulation using
  (left-guard-indexed; paired-guard-indexed; right-guard-indexed)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)

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
indexed-paired-generalized-instantiation
    {W} {W′} {α} {α′} {A} {A′} {c} {c′}
    {θ} {θ′} {V} {V′} simulation =
  indexed-simulation-pointwise
    (λ n → generalized-value-computation-eq
      {W = W} {α = α} {A = A} {c = c} {θ = θ} {V = V} n)
    (λ n → generalized-value-computation-eq
      {W = W′} {α = α′} {A = A′} {c = c′}
      {θ = θ′} {V = V′} n)
    (paired-guard-indexed simulation)

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
indexed-left-generalized-instantiation
    {W = W} {α = α} {A = A} {c = c} {θ = θ} {V = V}
    simulation =
  indexed-simulation-pointwise
    (λ n → generalized-value-computation-eq
      {W = W} {α = α} {A = A} {c = c} {θ = θ} {V = V} n)
    (λ n → refl)
    (left-guard-indexed simulation)

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
indexed-right-generalized-instantiation
    {W′ = W′} {α′ = α′} {A′ = A′} {c′ = c′}
    {θ′ = θ′} {V′ = V′} simulation =
  indexed-simulation-pointwise
    (λ n → refl)
    (λ n → generalized-value-computation-eq
      {W = W′} {α = α′} {A = A′} {c = c′}
      {θ = θ′} {V = V′} n)
    (right-guard-indexed simulation)
