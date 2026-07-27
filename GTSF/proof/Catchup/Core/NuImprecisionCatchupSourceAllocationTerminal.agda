module proof.Catchup.Core.NuImprecisionCatchupSourceAllocationTerminal where

-- File Charter:
--   * Freezes the nonrecursive terminal-value boundary for source-only
--     reveal-ν allocation catch-up.
--   * Frames an already-computed inner catch-up by `ν A`, stopping before the
--     allocation step and any subsequent recursive catch-up.
--   * The intended proofs weaken the source conversion evidence across the
--     supplied store prefix, then use the corresponding source frame together
--     with its transport and type-coherence preservation lemmas.
--   * Depends only on the quotiented precision judgment and the stable weak
--     simulation core.

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)

open import ImprecisionWf using
  (NonVar; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_; ν)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion; weaken-reveal-conversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NarrowWiden using (widen-weaken)
open import NuStore using (StoreIncl-cons)
open import NuTerms using (No•; Value; ok-no; ok-ν; ν)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (WfTy; occurs; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-source-ν-frameᵀ
  ; weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; left-indexed-catchup
  ; left-catchup-invariant
  ; left-silent-invariant
  ; left-silent-indexed
  ; sourceResult
  ; relatedResults
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-indexed-result
  ; catchupIndexedResult
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-source-liftνᵢ)

left-silent-indexed-prefix-source-ν-terminal-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N V′ s μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {occ : occurs zero C ≡ true}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
  (catchup : LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} (ν safe occ q)) →
  let inner = weakIndexedResult (catchupIndexedResult catchup) in
  Value (sourceResult inner) →
  No• (sourceResult inner) →
  LeftSilentIndexedResult
    {N = ν A N s} {V′ = V′} {ρ = ρ⁺} p
left-silent-indexed-prefix-source-ν-terminal-valueᵀ
    {p = p} prefix hA c↑ replace
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW =
  left-silent-indexed
    (weak-indexed-result framed (relatedResults framed)
      (weak-one-step-source-ν-frame-preserves-transportᵀ
        hA c↑⁺ p replace indexed (weakIndexedTransport indexed))
      (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
        hA c↑⁺ p replace indexed (weakIndexedTypeCoherence indexed)))
    (left-silent-invariant refl refl)
    (ok-ν (ok-no noW))
  where
  inner = weakIndexedResult indexed

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  c↑⁺ = weaken-reveal-conversion source-store-incl c↑

  framed = weak-one-step-source-ν-frameᵀ hA c↑⁺ p replace indexed
