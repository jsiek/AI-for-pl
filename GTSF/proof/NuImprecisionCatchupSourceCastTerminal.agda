module proof.NuImprecisionCatchupSourceCastTerminal where

-- File Charter:
--   * Freezes the arbitrary-type terminal-frame interface for source casts.
--   * Generalizes the completed universal-only terminal-frame lemmas from
--     `NuImprecisionSimulation` from `∀ⁱ r` to an arbitrary precision proof.
--   * Supplies the shared leaf obligations needed by the five source
--     cast/conversion clauses of general indexed left catch-up.
--   * Contains the source-blame and source-inert terminal-frame proofs.
--   * Depends on the stable weak-simulation core, source-keep composition
--     helpers, and base judgments.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.HeterogeneousEquality as HE

open import Coercions using (Inert)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (blame-⟨⟩; keep; pure-step)
open import NuTerms using (blame; no•-⟨⟩; _⟨_⟩)
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; nu-term-imprecision-target-typing
  )
import proof.NuImprecisionCatchupComposition as CC
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
left-catchup-indexed-source-cast-blame-frameᵀ
    {q = q}
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    framed refl (left-silent-invariant refl refl)
    first-transport first-coherence refl =
  left-indexed-catchup
    (weak-one-step-index-resultᵀ combined type-eq)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₂ refl))
    combined-transport combined-coherence
  where
  first-raw = weakIndexedResult framed

  first = weak-one-step-reindexᵀ
    first-raw refl refl (canonicalIndexedResults framed)

  first-transport′ =
    weak-one-step-reindex-preserves-transportᵀ
      first-raw refl refl (canonicalIndexedResults framed)
      first-transport

  first-coherence′ =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      first-raw refl refl (canonicalIndexedResults framed)
      first-coherence

  target⊢ =
    nu-term-imprecision-target-typing (relatedResults first)

  second-relation = blame⊑ᵀ target⊢

  second = CC.weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (pure-step blame-⟨⟩) second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-transport′
      (CC.weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-coherence′
      (CC.weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) second-relation)

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
left-catchup-indexed-source-inert-frameᵀ
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    with final
left-catchup-indexed-source-inert-frameᵀ
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    | inj₁ (vW , noW) =
  left-indexed-catchup framed
    (left-catchup-invariant first-silent
      (inj₁ (vW ⟨ inert ⟩ , no•-⟨⟩ noW)))
    first-transport first-coherence
left-catchup-indexed-source-inert-frameᵀ
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    | inj₂ refl =
  left-catchup-indexed-source-cast-blame-frameᵀ
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence refl
