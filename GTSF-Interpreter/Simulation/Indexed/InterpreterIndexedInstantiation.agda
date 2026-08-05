module Simulation.Indexed.InterpreterIndexedInstantiation where

-- File Charter:
--   * Exposes positive-index composition for paired and left-only term
--     instantiation.
--   * Takes operand and post-allocation tail simulations explicitly.
--   * Delegates the reduction-free indexed sequencing proofs to `proof/`.

open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import Data.Nat
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
import proof.InterpreterIndexedInstantiationProof as Proof
open import proof.InterpreterInstantiationTail using
  (instantiation-tail)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-paired-instantiation-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ A A′ L L′ c c′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      left-index right-index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-paired-instantiation-suc-simulation =
  Proof.indexed-paired-instantiation-suc-simulation

indexed-left-instantiation-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ A L c N′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      left-index right-index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    (Data.Nat.suc left-index)
    right-index
indexed-left-instantiation-suc-simulation =
  Proof.indexed-left-instantiation-suc-simulation
