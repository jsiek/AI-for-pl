module Simulation.Framed.InterpreterFramedSealCoercion where

-- File Charter:
--   * Exposes exact positive-fuel simulation for paired seal coercions.
--   * Retains the framed input beneath the two sealed results.
--   * Uses runtime store realization to identify concrete related seal names.
--   * Delegates reduction-free construction to a focused proof module.

open import Coercions renaming (seal to sealᶜ)
open import Data.Nat using (suc)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedSealCoercionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


indexed-framed-paired-seal :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ C D X Y p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (sealᶜ C X))
      (apply-coercion (sealᶜ D Y))
      {A} {A′} {＇ X} {＇ Y} p q) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (sealᶜ C X) V)
    (coerceValue W′ θ′ (sealᶜ D Y) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-seal =
  Proof.indexed-framed-paired-seal
