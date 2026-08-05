module Simulation.Polymorphism.InterpreterInstantiationSimulation where

-- File Charter:
--   * Public compositional simulation theorem for paired term instantiation.
--   * Takes recursive operand and allocation/instantiation/coercion-tail
--     simulations explicitly for use by the later mutual driver.
--   * Delegates asynchronous sequencing to its focused proof module.

open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Simulation.Core.InterpreterTermSimulationMotive
open import Narrowing.InterpreterTypedValueNarrowing
import NuTerms as N
import proof.InterpreterInstantiationSimulationCases as Proof
open import proof.InterpreterInstantiationTail using
  (instantiation-tail)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-instantiation-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      A A′ L L′ c c′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypedValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    TerminalSimulation
      (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)) →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
paired-instantiation-term-simulation =
  Proof.paired-instantiation-term-simulation

left-instantiation-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      A L c N′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypedValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    TerminalSimulation
      (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)) →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
left-instantiation-term-simulation =
  Proof.left-instantiation-term-simulation
