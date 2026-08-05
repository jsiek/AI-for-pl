module proof.InterpreterFramedTermSimpleProof where

-- File Charter:
--   * Proves exact indexed variable, closure, and constant simulations.
--   * Uses direct interpreter equations and exact environment/value origins.
--   * Contains no small-step reduction, divergence negation, or catch-up.

open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_; _↦_; idι)
open import Interpreter
open import Runtime.InterpreterClosedValue using
  (ClosedValue; closed-closure; closed-constant)
open import Runtime.InterpreterCloseFramedValue using
  (close-aligned-framed)
open import Simulation.Framed.InterpreterFramedEnvironmentLookup using
  (framed-environment-lookup)
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
open import proof.InterpreterCloseOperationalValueProof using
  (typed-closed-aligned)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
import proof.InterpreterTermSimulationSimpleCases as Simple
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
indexed-framed-variable {runtime = runtime} origins x∈
    with framed-environment-lookup origins x∈
indexed-framed-variable {runtime = runtime} origins x∈
    | V , V′ , left-eq , right-eq , value =
  indexed-simulation-pointwise
    (Simple.variable-computation-eq left-eq)
    (Simple.variable-computation-eq right-eq)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime value)))

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
indexed-framed-closure
    {runtime = runtime} environment origins unique alignment =
  indexed-simulation-pointwise
    Simple.closure-computation-eq
    Simple.closure-computation-eq
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (close-aligned-framed
            unique
            alignment runtime environment origins
            closed-closure closed-closure))))

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
indexed-framed-constant
    {n = n} {runtime = runtime} environment origins =
  indexed-simulation-pointwise
    Simple.constant-computation-eq
    Simple.constant-computation-eq
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value
            (typed-closed-aligned
              constant-aligned runtime environment
              (closed-constant (Primitives.κℕ n))
              (closed-constant (Primitives.κℕ n)))
            (operational-value
              (typed-closed-aligned
                constant-aligned runtime environment
                (closed-constant (Primitives.κℕ n))
                (closed-constant (Primitives.κℕ n)))
              constant-origin)
            constant-originᶠ))))
