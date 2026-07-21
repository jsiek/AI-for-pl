module
  proof.NuImprecisionWorldCoherentFinalPairedConversionCatchupProof
  where

-- File Charter:
--   * Proves exact-world terminal catch-up for paired conversions.
--   * Handles source identities, inert conversions, and source blame.
--   * Eliminates source unseal against an inert target by type precision.
--   * Imports no recursive runtime or value-catch-up dispatcher.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Coercions using
  ( Inert
  ; seal
  ; _↦_
  ; `∀
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( β-id
  ; blame-⟨⟩
  ; pure-step
  )
open import NuTerms using
  ( no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-target-typing
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; prefix-reflⁱ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Types using (＇_; ★; _⇒_; `∀)
open import proof.NuImprecisionCatchupComposition using
  (left-catchup-indexed-prepend-keepᵀ)
open import proof.NuImprecisionCatchupPrefixSupport using
  ( left-catchup-indexed-prefix-blameᵀ
  ; left-catchup-indexed-prefix-valueᵀ
  )
open import proof.NuImprecisionQuotientValue using
  (left-catchup-indexed-one-keep-valueᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalPairedConversionCatchupDef
  using (WorldCoherentFinalPairedConversionCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)


source-unseal-target-inert-impossible :
  ∀ {Φ Δᴸ Δᴿ μ Σ α β X c′ A′ B′} →
  Inert c′ →
  RevealConversion μ Δᴿ Σ β X c′ A′ B′ →
  Φ ∣ Δᴸ ⊢ ＇ α ⊑ A′ ⊣ Δᴿ →
  ⊥
source-unseal-target-inert-impossible
    () (reveal-id-var hY ok) p
source-unseal-target-inert-impossible
    () reveal-id-base p
source-unseal-target-inert-impossible
    () reveal-id-★ p
source-unseal-target-inert-impossible
    () (reveal-unseal hX β∈Σ ok) p
source-unseal-target-inert-impossible
    inert (reveal-fun s↓ t↑) ()
source-unseal-target-inert-impossible
    inert (reveal-all s↑) ()

world-coherent-final-paired-conversion-catchup-proofᵀ :
  WorldCoherentFinalPairedConversionCatchupᵀ
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₂ refl) vV′ noV′ inert-c′
    conversion W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prepend-keepᵀ
      (pure-step blame-⟨⟩)
      (left-catchup-indexed-prefix-blameᵀ
        prefix-reflⁱ (no•-⟨⟩ noV′)
        (blame⊑ᵀ target⊢)))
    coherent exclusive wfL
  where
  target⊢ = nu-term-imprecision-target-typing
    (conv⊑convᵀ (paired-conversion conversion) W⊑V′)
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-reveal corr (reveal-id-var hY ok) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↑ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-reveal corr reveal-id-base target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↑ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-reveal corr reveal-id-★ target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↑ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    {p = p} coherent exclusive wfL (inj₁ (vW , noW))
    vV′ noV′ inert-c′
    (paired-reveal corr (reveal-unseal hX α∈Σ ok) target) W⊑V′ =
  ⊥-elim (source-unseal-target-inert-impossible inert-c′ target p)
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    conversion@(paired-reveal corr (reveal-fun s↓ t↑) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ _ ↦ _ ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    conversion@(paired-reveal corr (reveal-all s↑) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ `∀ _ ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-conceal corr (conceal-id-var hY ok) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↓ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-conceal corr conceal-id-base target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↓ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-conceal corr conceal-id-★ target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-one-keep-valueᵀ
      (pure-step (β-id vW)) vW noW
      (⊑conv↓ᵀ target W⊑V′ _))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    conversion@(paired-conceal corr (conceal-seal hX α∈Σ ok) target)
    W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ seal _ _ ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    conversion@(paired-conceal corr (conceal-fun s↑ t↓) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ _ ↦ _ ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
    coherent exclusive wfL
world-coherent-final-paired-conversion-catchup-proofᵀ
    coherent exclusive wfL (inj₁ (vW , noW)) vV′ noV′ inert-c′
    conversion@(paired-conceal corr (conceal-all s↓) target) W⊑V′ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix-reflⁱ (ok-no (no•-⟨⟩ noW)) (vW ⟨ `∀ _ ⟩)
      (no•-⟨⟩ noV′)
      (conv⊑convᵀ (paired-conversion conversion) W⊑V′))
    coherent exclusive wfL
