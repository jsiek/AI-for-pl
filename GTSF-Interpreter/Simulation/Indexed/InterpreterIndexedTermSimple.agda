module Simulation.Indexed.InterpreterIndexedTermSimple where

-- File Charter:
--   * Exposes the indexed variable, closure, and constant term cases.
--   * Returns exact operational value origins rather than independently
--     chosen unary typings.
--   * Delegates the reduction-free proofs to a focused private module.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using
  (WorldTyping; base-type; _⇒ᵛ_; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
open import Types
import proof.InterpreterIndexedTermSimpleProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-variable-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  IndexedTerminalSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x))
    left-index right-index
indexed-variable-simulation =
  Proof.indexed-variable-simulation

indexed-closure-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
      (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]))
    R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′))
    left-index right-index
indexed-closure-simulation =
  Proof.indexed-closure-simulation

indexed-constant-simulation :
  ∀ {left-index right-index W W′ γ γ′ θ θ′ n}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n)))
    left-index right-index
indexed-constant-simulation =
  Proof.indexed-constant-simulation
