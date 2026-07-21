module proof.NuImprecisionWorldCoherentSourceNarrowCatchupProof where

-- File Charter:
--   * Proves coherent catch-up through one source narrowing cast.
--   * Dispatches exhaustively on the narrowing coercion grammar.
--   * Reuses the strict source-cast frame and coherent silent-resume helpers.
--   * Keeps the recursive value catch-up capability as a whole dependency.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import NarrowWiden using (narrow-weaken)
import NarrowWiden as NW
open import NuTerms using (ok-no; ok-⟨⟩)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.NuImprecisionCatchupSourceCastTerminal using
  (left-catchup-indexed-source-cast-blame-frameᵀ)
open import proof.NuImprecisionSimulation using
  (weak-one-step-source-narrow-cast-indexed-frameᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import proof.NuImprecisionWorldCoherentSourceNarrowCatchupDef using
  (WorldCoherentSourceNarrowCatchupᵀ)
open import proof.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)
open import proof.TypePreservation using (seal★-weaken)


world-coherent-source-narrow-catchup-framedᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentSourceNarrowCatchupᵀ
world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ c⊒ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    with final
world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ c⊒ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no noW))
      first-transport first-coherence)
    (value-catchup
      prefix-reflⁱ coherent exclusive wfL
      (ok-⟨⟩ (ok-no noW)) vV′ noV′
      (canonicalIndexedResults framed))
  where
  source-store-incl = leftStoreⁱ-prefix-inclusion prefix

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊒⁺ = narrow-weaken ≤-refl source-store-incl c⊒

  framed =
    weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★⁺ c⊒⁺ indexed

  first-transport =
    weak-step-transport (transportNo•Terms inner-transport)

  first-coherence =
    weak-step-type-coherence
      (transportArrowCoherent inner-coherence)
      (transportAllCoherent inner-coherence)
world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ c⊒ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL)
    q
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl (left-silent-invariant refl refl)
      first-transport first-coherence refl)
    coherent exclusive wfL
  where
  source-store-incl = leftStoreⁱ-prefix-inclusion prefix

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊒⁺ = narrow-weaken ≤-refl source-store-incl c⊒

  framed =
    weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★⁺ c⊒⁺ indexed

  first-transport =
    weak-step-transport (transportNo•Terms inner-transport)

  first-coherence =
    weak-step-type-coherence
      (transportArrowCoherent inner-coherence)
      (transportAllCoherent inner-coherence)


world-coherent-source-narrow-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentSourceNarrowCatchupᵀ
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.id-＇ α)) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.id-＇ α))
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.id-‵ ι)) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.id-‵ ι))
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (sʷ NW.↦ tⁿ)) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (sʷ NW.↦ tⁿ))
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.`∀ sⁿ)) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★
    (c⊢ , NW.cross (NW.`∀ sⁿ))
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.id★) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.id★)
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.gen sⁿ) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.gen sⁿ)
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.untag gG) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.untag gG)
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , gG NW.？︔ gˢ) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , gG NW.？︔ gˢ)
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.sealⁿ A α) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , NW.sealⁿ A α)
world-coherent-source-narrow-catchup-proofᵀ
    value-catchup prefix mode seal★ (c⊢ , sˢ NW.︔seal α) =
  world-coherent-source-narrow-catchup-framedᵀ
    value-catchup prefix mode seal★ (c⊢ , sˢ NW.︔seal α)
