module proof.InterpreterTermSimulationTypingProof where

-- File Charter:
--   * Upgrades an open term simulation with endpoint semantic typing.
--   * Obtains both unary interpreter-typing proofs from the synchronized
--     runtime configuration and the static narrowing certificate.
--   * Contains no evaluator recursion or reduction semantics.

open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (interpret-preserves-semantic-typing)
open import Typing.InterpreterSemanticTypingCore using
  (OutcomeTyping; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Simulation.Core.InterpreterTypedSimulation
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
open import TermTyping using (forget)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

source-interpret-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  RuntimeTypeEnvironment θ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  ∀ n →
  OutcomeTyping W ⟦ A ⟧[ θ ] (interpret W γ θ N n)
source-interpret-typing
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ} {N = N} {N′ = N′} {A = A} {B = B}
    {runtime = runtime} runtime-env environment terms n =
  interpret-preserves-semantic-typing n
    (left-world-typed runtime)
    (left-runtime-context runtime)
    runtime-env
    (left-environment-typed environment)
    (interpreter-narrowing-source-term (term-shape terms))
    (forget (open-interpreter-narrowing-source-typing
      {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γ = γᵀ} {N = N} {N′ = N′}
      {A = A} {B = B} terms))

target-interpret-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  ∀ n →
  OutcomeTyping W′ ⟦ B ⟧[ θ′ ] (interpret W′ γ′ θ′ N′ n)
target-interpret-typing
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ} {N = N} {N′ = N′} {A = A} {B = B}
    {runtime = runtime} environment terms n =
  interpret-preserves-semantic-typing n
    (right-world-typed runtime)
    (right-runtime-context runtime)
    (right-runtime-environment runtime)
    (right-environment-typed environment)
    (interpreter-narrowing-target-term (term-shape terms))
    (forget (open-interpreter-narrowing-target-typing
      {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γ = γᵀ} {N = N} {N′ = N′}
      {A = A} {B = B} terms))

term-typed-result-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  RuntimeTypeEnvironment θ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′) →
  TerminalSimulation
    (TypedValueResult ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ])
    R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
term-typed-result-simulation
    {runtime = runtime} runtime-env environment terms simulation =
  typed-result-simulation simulation
    (source-interpret-typing runtime-env environment terms)
    (target-interpret-typing environment terms)
