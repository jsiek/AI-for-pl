module
  proof.NuImprecisionWorldCoherentFinalPairedWideningCatchupProof
  where

-- File Charter:
--   * Proves exact-world terminal catch-up for compatible paired widenings.
--   * Uses source inertness for the zero-step terminal case and the explicit
--     cross bridge for the source-widen/target-frame case.
--   * Takes only the source-widen handler contract and imports no source
--     runtime record or implementation.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import NuReduction using
  ( blame-⟨⟩
  ; pure-step
  )
open import NuTerms using
  ( no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  ( compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-target-typing
  ; paired-widening
  ; prefix-reflⁱ
  )
open import proof.NuImprecisionCatchupComposition using
  (left-catchup-indexed-prepend-keepᵀ)
open import proof.NuImprecisionCatchupPrefixSupport using
  ( left-catchup-indexed-prefix-blameᵀ
  ; left-catchup-indexed-prefix-valueᵀ
  )
open import proof.NuImprecisionWorldCoherentCatchupPrefixFrames using
  (world-coherent-left-catchup-prefix-target-widen-castᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalPairedWideningCatchupDef
  using (WorldCoherentFinalPairedWideningCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import proof.NuImprecisionWorldCoherentSourceWidenCatchupDef using
  (WorldCoherentSourceWidenCatchupᵀ)


world-coherent-final-paired-widening-catchup-proofᵀ :
  WorldCoherentSourceWidenCatchupᵀ →
  WorldCoherentFinalPairedWideningCatchupᵀ
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen {p = p} {q = q}
    coherent exclusive wfL (inj₂ refl) vV′ noV′ inert-c′
    mode seal★ c⊑ mode′ seal★′ c′⊑ compat W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prepend-keepᵀ
      (pure-step blame-⟨⟩)
      (left-catchup-indexed-prefix-blameᵀ
        prefix-reflⁱ (no•-⟨⟩ noV′)
        (blame⊑ᵀ target⊢)))
    coherent exclusive wfL
  where
  target⊢ = nu-term-imprecision-target-typing
    (conv⊑convᵀ
      (paired-widening
        {p = p} {q = q}
        mode seal★ c⊑ mode′ seal★′ c′⊑ compat)
      W⊑V′)
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′
    inert-c′ mode seal★ c⊑ mode′ seal★′ c′⊑
    (compatible-source-inert inert-c) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ inert-c ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ
        (paired-widening
          mode seal★ c⊑ mode′ seal★′ c′⊑
          (compatible-source-inert inert-c))
        W⊑V′))
    coherent exclusive wfL
world-coherent-final-paired-widening-catchup-proofᵀ
    source-widen coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′
    inert-c′ mode seal★ c⊑ mode′ seal★′ c′⊑
    (compatible-target-inert-bridge bridge) W⊑V′ =
  world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix-reflⁱ mode′ seal★′ c′⊑ source-catchup
  where
  initial =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no noW) vW noV′ W⊑V′)
      coherent exclusive wfL

  source-catchup =
    source-widen prefix-reflⁱ mode seal★ c⊑
      vV′ noV′ initial (bridge inert-c′)
