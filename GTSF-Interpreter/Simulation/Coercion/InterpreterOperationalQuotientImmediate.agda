module Simulation.Coercion.InterpreterOperationalQuotientImmediate where

-- File Charter:
--   * Publicly exposes positive-fuel execution of inert quotient downcasts.
--   * States the exact operational intermediate returned by both endpoints.
--   * Delegates the reduction-free proof to a focused private module.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
open import Data.Nat using (suc)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterCoercionNarrowing
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
import proof.InterpreterOperationalQuotientImmediateProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-quotient-down-inert :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ X Y E d d′ V V′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (down :
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC
      (endpoint-representatives-quotient D⊑E alignment)) →
  Inert d →
  Inert d′ →
  FramedValueNarrowing
    {A = C} {A′ = C′} {p = pC} runtime V V′ →
  IndexedTerminalSimulation
    (OperationalQuotientValueNarrowing
      runtime d d′ D⊑E alignment down)
    R
    (coerceValue W θ d V)
    (coerceValue W′ θ′ d′ V′)
    (suc left-index) (suc right-index)
indexed-quotient-down-inert =
  Proof.indexed-quotient-down-inert

indexed-quotient-up-inert :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ A A′ X Y E d d′ u u′}
    {V V′ L L′ : Value}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left-down-inert : Inert d}
    {right-down-inert : Inert d′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (down :
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC
      (endpoint-representatives-quotient D⊑E alignment)) →
  (up : OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ u u′
      (endpoint-representatives-quotient D⊑E alignment) pA) →
  (left-up-inert : Inert u) →
  (right-up-inert : Inert u′) →
  (value :
    FramedValueNarrowing
      {A = C} {A′ = C′} {p = pC} runtime V V′) →
  ClosedValueFrame θ V left-down-inert L →
  ClosedValueFrame θ′ V′ right-down-inert L′ →
  (∀ n → coerceValue W θ d V (suc n)
    ≡ returned W L) →
  (∀ n → coerceValue W′ θ′ d′ V′ (suc n)
    ≡ returned W′ L′) →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ pA) R
    (coerceValue W θ u L)
    (coerceValue W′ θ′ u′ L′)
    (suc left-index) (suc right-index)
indexed-quotient-up-inert =
  Proof.indexed-quotient-up-inert
