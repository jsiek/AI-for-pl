module Simulation.Framed.InterpreterFramedGeneralizationCoercion where

-- File Charter:
--   * Exposes exact positive-fuel simulations for generalization coercions.
--   * Retains the executable coercion action in each generalized origin.
--   * Delegates reduction-free construction to a focused proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (gen)
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
import proof.InterpreterFramedGeneralizationCoercionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-paired-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q C C′ c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) (apply-coercion (gen C′ c′))
      {A} {A′} {`∀ B} {`∀ B′} p (∀ⁱ q)) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (∀ⁱ q)) R
    (coerceValue W θ (gen C c) V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-generalization-coercion =
  Proof.indexed-framed-paired-generalization-coercion

indexed-framed-left-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q C c V V′}
    {nonvar : NonVar B} {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) skip-coercion
      {A} {T} {`∀ B} {T} p (ν nonvar occ q)) →
  FramedValueNarrowing
    {A = A} {A′ = T} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar occ q)) R
    (coerceValue W θ (gen C c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-generalization-coercion =
  Proof.indexed-framed-left-generalization-coercion

indexed-framed-right-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S A′ B′ p q C′ c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (gen C′ c′))
      {S} {A′} {S} {`∀ B′} p q) →
  FramedValueNarrowing
    {A = S} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    left-index (suc right-index)
indexed-framed-right-generalization-coercion =
  Proof.indexed-framed-right-generalization-coercion
