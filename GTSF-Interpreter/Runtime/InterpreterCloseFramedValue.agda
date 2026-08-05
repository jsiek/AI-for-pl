module Runtime.InterpreterCloseFramedValue where

-- File Charter:
--   * Exposes exact closing of compiler-aligned syntactic values.
--   * Retains the static precision derivation, runtime frame, and future
--     polymorphic allocation behavior in the returned relation.
--   * Delegates the structural proof to a reduction-free private module.

open import Interpreter
open import Runtime.InterpreterClosedValue
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
import proof.InterpreterCloseFramedValueProof as Proof
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

close-aligned-framed :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p) →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  FramedValueNarrowing
    {A = A} {A′ = B} {p = p} runtime U U′
close-aligned-framed =
  Proof.close-aligned-framed
