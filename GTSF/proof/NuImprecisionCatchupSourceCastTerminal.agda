{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionCatchupSourceCastTerminal where

-- File Charter:
--   * Freezes the arbitrary-type terminal-frame interface for source casts.
--   * Generalizes the completed universal-only terminal-frame lemmas from
--     `NuImprecisionSimulation` from `∀ⁱ r` to an arbitrary precision proof.
--   * Supplies the shared leaf obligations needed by the five source
--     cast/conversion clauses of general indexed left catch-up.
--   * Contains exactly two intended proof holes, one for a caught source
--     blame and one for a source inert-cast value.
--   * Depends only on the stable weak-simulation core and base judgments.

open import Agda.Builtin.Equality using (_≡_)

open import Coercions using (Inert)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTerms using (blame; _⟨_⟩)
open import NuTermImprecision using (StoreImp)
open import proof.NuImprecisionSimulationCore

left-catchup-indexed-source-cast-blame-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M L V′ A A′ B B′ ρ d}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  (framed : WeakOneStepIndexedResult
    {M = L} {N′ = V′} {χ = keep} {ρ = ρ} q) →
  let inner = weakIndexedResult (catchupIndexedResult catchup)
      first = weakIndexedResult framed
  in
  sourceResult first ≡ sourceResult inner ⟨ d ⟩ →
  LeftSilentInvariant first →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  sourceResult inner ≡ blame →
  LeftCatchupIndexedResult
    {N = L} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-source-cast-blame-frameᵀ = {!!}

left-catchup-indexed-source-inert-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M L V′ A A′ B B′ ρ d}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Inert d →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  (framed : WeakOneStepIndexedResult
    {M = L} {N′ = V′} {χ = keep} {ρ = ρ} q) →
  let inner = weakIndexedResult (catchupIndexedResult catchup)
      first = weakIndexedResult framed
  in
  sourceResult first ≡ sourceResult inner ⟨ d ⟩ →
  LeftSilentInvariant first →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  LeftCatchupIndexedResult
    {N = L} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-source-inert-frameᵀ = {!!}
