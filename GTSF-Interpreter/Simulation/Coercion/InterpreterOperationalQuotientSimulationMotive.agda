module Simulation.Coercion.InterpreterOperationalQuotientSimulationMotive where

-- File Charter:
--   * States the direction-specific motives for executing quotient downcasts
--     into, and quotient upcasts out of, the operational intermediate.
--   * Keeps allocating result worlds explicit in the intermediate relation.
--   * Retains the compiler-selected route alignment and exact runtime frame.
--   * Contains no recursion, interpreter equation, or small-step reduction.

import Level

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalQuotientValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

DirectionalQuotientDownSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalQuotientDownSimulation direction index =
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ X Y E d d′ V V′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (down :
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC
      (endpoint-representatives-quotient D⊑E alignment)) →
  FramedValueNarrowing
    {A = C} {A′ = C′} {p = pC} runtime V V′ →
  DirectionalObservation direction
    (OperationalQuotientValueNarrowing
      runtime d d′ D⊑E alignment down)
    R
    (coerceValue W θ d V)
    (coerceValue W′ θ′ d′ V′)
    index

DirectionalQuotientUpSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalQuotientUpSimulation direction index =
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ A A′ X Y E d d′ u u′ L L′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {down :
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment)} →
  AssumptionMembershipUnique Φ →
  (up : OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ u u′
      (endpoint-representatives-quotient D⊑E alignment) pA) →
  OperationalQuotientValueNarrowing
    runtime d d′ D⊑E alignment down S L L′ →
  DirectionalObservation direction
    (FramedValueResult ρ θ θ′ pA)
    S
    (coerceValue U θ u L)
    (coerceValue U′ θ′ u′ L′)
    index
