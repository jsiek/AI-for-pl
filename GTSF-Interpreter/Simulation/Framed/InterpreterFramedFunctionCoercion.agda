module Simulation.Framed.InterpreterFramedFunctionCoercion where

-- File Charter:
--   * Exposes exact positive-fuel simulations for inert function coercions.
--   * Retains domain and codomain component actions in returned origins.
--   * Delegates reduction-free construction to a focused proof module.

open import Coercions using (_↦_)
open import Data.Nat using (suc)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (ReachableComponentCoercionNarrowing)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedFunctionCoercionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-paired-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ C C′ D D′ pA pB pC pD
      c d c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) (apply-coercion (c′ ↦ d′))
      {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (coerceValue W θ (c ↦ d) V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-function-coercion =
  Proof.indexed-framed-paired-function-coercion

indexed-framed-left-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A B C D T₁ T₂ pA pB pC pD c d V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) skip-coercion
      {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = T₁ ⇒ T₂}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (coerceValue W θ (c ↦ d) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-function-coercion =
  Proof.indexed-framed-left-function-coercion

indexed-framed-right-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (c′ ↦ d′))
      {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  FramedValueNarrowing
    {A = S₁ ⇒ S₂} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (pC ImprecisionWf.↦ pD)) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    left-index (suc right-index)
indexed-framed-right-function-coercion =
  Proof.indexed-framed-right-function-coercion
