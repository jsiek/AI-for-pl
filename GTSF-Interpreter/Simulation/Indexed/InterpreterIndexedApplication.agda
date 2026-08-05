module Simulation.Indexed.InterpreterIndexedApplication where

-- File Charter:
--   * Exposes positive-index composition for compiler-aligned applications.
--   * Takes function, argument, and semantic-application simulations
--     explicitly.
--   * Delegates the reduction-free indexed sequencing proof to `proof/`.

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
import Data.Nat
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
import proof.InterpreterIndexedApplicationProof as Proof
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
indexed-application-suc-simulation =
  Proof.indexed-application-suc-simulation
