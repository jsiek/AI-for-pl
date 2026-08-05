module Simulation.Framed.InterpreterFramedForallCoercion where

-- File Charter:
--   * Exposes exact positive-fuel simulations for inert forall coercions.
--   * Retains lifted store and body-component actions in returned origins.
--   * Delegates reduction-free construction to a focused proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (`∀)
open import Data.Bool using (true)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  (NonVar; _∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedForallCoercionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-paired-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (coerceValue W θ (`∀ c) V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-forall-coercion =
  Proof.indexed-framed-paired-forall-coercion

indexed-framed-left-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q c V V′}
    {nonvar : NonVar A} {occ : occurs zero A ≡ true}
    {nonvar′ : NonVar B} {occ′ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) skip-coercion
      {`∀ A} {T} {`∀ B} {T}
      (ν nonvar occ p) (ν nonvar′ occ′ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = T}
    {p = ν nonvar occ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar′ occ′ q)) R
    (coerceValue W θ (`∀ c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-forall-coercion =
  Proof.indexed-framed-left-forall-coercion

indexed-framed-right-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B′ p q c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ A} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  FramedValueNarrowing
    {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    left-index (suc right-index)
indexed-framed-right-forall-coercion =
  Proof.indexed-framed-right-forall-coercion
