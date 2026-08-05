module Simulation.Framed.InterpreterFramedTypeAbstraction where

-- File Charter:
--   * Exposes exact indexed simulation for paired type abstractions.
--   * Keeps the ambient runtime frame while closing both syntactic values.
--   * Delegates the reduction-free proof to a focused private module.

open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import proof.InterpreterFramedTypeAbstractionProof as Proof
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-paired-type-abstraction :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′))
    left-index right-index
indexed-framed-paired-type-abstraction =
  Proof.indexed-framed-paired-type-abstraction
