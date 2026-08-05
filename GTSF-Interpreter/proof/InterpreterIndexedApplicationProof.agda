module proof.InterpreterIndexedApplicationProof where

-- File Charter:
--   * Proves positive-index application simulation by two indexed chains.
--   * Weakens the exact runtime, environment, and operational origins at
--     every returned-world extension.
--   * Uses direct interpreter equations and unary terminal stability only.

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
import Data.Nat
open import Data.Product using (_,_)

open import Interpreter
open import Core.InterpreterFuel using
  (applyValue-terminal-stable; interpret-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Narrowing.InterpreterTypedValueNarrowing
import NuTerms as N
open import proof.InterpreterApplicationTail
open import proof.InterpreterIndexedChainSimulation using
  (indexed-chain-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-application-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  IndexedApplyValueSimulation left-index right-index →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-application-suc-simulation
    {W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {L = L} {L′} {M} {M′} {B = B} {B′}
    {R = R} {runtime = runtime}
    environment origins terms
    function-simulation argument-simulation apply-simulation
    with application-open-operands terms
indexed-application-suc-simulation
    {left-index} {right-index}
    {W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {L = L} {L′} {M} {M′} {B = B} {B′}
    {R = R} {runtime = runtime}
    environment origins terms
    function-simulation argument-simulation apply-simulation
    | A , A′ , pA , function-terms , argument-terms =
  indexed-simulation-pointwise
    application-computation-eq
    application-computation-eq
    (indexed-sequence-simulation
      (function-simulation
        runtime environment origins function-terms)
      tail-simulation
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = L}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = L′}
          {n = n} {o = o} terminal eq k
        })
      (λ u v {n} {o} terminal eq k →
        application-tail-stable
          {W = u} {γ = γ} {θ = θ} {M = M} {V = v}
          {n = n} {o = o} terminal eq k)
      (λ u′ v′ {n} {o} terminal eq k →
        application-tail-stable
          {W = u′} {γ = γ′} {θ = θ′} {M = M′} {V = v′}
          {n = n} {o = o} terminal eq k))
  where
  tail-simulation :
    ∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      (⟦ A ⇒ B ⟧[ θ ]) (⟦ A′ ⇒ B′ ⟧[ θ′ ]) S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (application-tail U γ θ M V)
      (application-tail U′ γ′ θ′ M′ V′)
      left-index right-index
  tail-simulation
      {U = u} {U′ = u′} {V = v} {V′ = v′} {S = relation}
      R≤S V~V′ =
    indexed-chain-simulation
      (argument-simulation
        weakened-runtime weakened-environment weakened-origins
        (open-interpreter-narrowing-world-weaken
          R≤S argument-terms))
      (λ S≤T U~U′ →
        apply-simulation
          (operational-value-narrowing-weaken
            S≤T
            (left-world-typed (operational-typed U~U′))
            (right-world-typed (operational-typed U~U′))
            V~V′)
          U~U′)
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = u} {γ = γ} {θ = θ} {M = M}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = u′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ z q {n} {o} terminal eq k →
        applyValue-terminal-stable
          {W = z} {V = v} {U = q}
          {n = n} {o = o} terminal eq k)
      (λ z′ q′ {n} {o} terminal eq k →
        applyValue-terminal-stable
          {W = z′} {V = v′} {U = q′}
          {n = n} {o = o} terminal eq k)
    where
    weakened-runtime =
      runtime-narrowing-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        runtime

    weakened-environment =
      environment-realization-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        environment

    weakened-origins =
      operational-environment-narrowing-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        origins
