module Simulation.Framed.InterpreterFramedBasicCoercion where

-- File Charter:
--   * EXPERIMENTAL (O34): tag cases still need the executable-runtime
--     readiness premise introduced by the corrected ground classifier.
--   * Exposes exact positive-fuel identity and ground-tag simulations.
--   * Reindexes unchanged identity results and records exact tag origins.
--   * Delegates reduction-free construction to a focused proof module.

open import Coercions renaming (id to idᶜ; _! to _!ᶜ)
open import Data.Nat using (suc)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedBasicCoercionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-paired-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (idᶜ A) V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-id =
  Proof.indexed-framed-paired-id

indexed-framed-left-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (idᶜ A) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-id =
  Proof.indexed-framed-left-id

indexed-framed-right-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
    left-index (suc right-index)
indexed-framed-right-id =
  Proof.indexed-framed-right-id

indexed-framed-paired-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ G H p q V V′}
    {gG : Ground G} {gH : Ground H}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (G !ᶜ)) (apply-coercion (H !ᶜ))
      {A} {A′} {★} {★} p q) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (G !ᶜ) V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-tag {gG = gG} {gH = gH} =
  Proof.indexed-framed-paired-tag {gG = gG} {gH = gH}

indexed-framed-left-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A G p q V V′}
    {gG : Ground G}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (G !ᶜ)) skip-coercion
      {A} {★} {★} {★} p q) →
  FramedValueNarrowing
    {A = A} {A′ = ★} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (G !ᶜ) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-tag {gG = gG} =
  Proof.indexed-framed-left-tag {gG = gG}

indexed-framed-right-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A′ H p q V V′}
    {gH : Ground H}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (H !ᶜ))
      {★} {A′} {★} {★} p q) →
  FramedValueNarrowing
    {A = ★} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
    left-index (suc right-index)
indexed-framed-right-tag {gH = gH} =
  Proof.indexed-framed-right-tag {gH = gH}
