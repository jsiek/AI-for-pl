module Simulation.Framed.InterpreterFramedTermSimple where

-- File Charter:
--   * Exposes exact indexed variable, closure, and constant simulations.
--   * Returns runtime-framed values at their static precision indices.
--   * Delegates interpreter equations and case proofs to a private module.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_; _↦_; idι)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
import proof.InterpreterFramedTermSimpleProof as Proof
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-variable :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x))
    left-index right-index
indexed-framed-variable =
  Proof.indexed-framed-variable

indexed-framed-closure :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pA ↦ pB)) R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′))
    left-index right-index
indexed-framed-closure =
  Proof.indexed-framed-closure

indexed-framed-constant :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ n}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ idι) R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n)))
    left-index right-index
indexed-framed-constant =
  Proof.indexed-framed-constant
