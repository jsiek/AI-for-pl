module proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceCastFrameStepProof where

-- File Charter:
--   * Proves the higher-order fit of source cast congruence against every
--     quotiented term-imprecision constructor that can expose a source cast.
--   * Recurses only through the supplied source-step prefix capability and
--     maps its existing outcome directly through source, target, and paired
--     frames.
--   * Contains no canonical recursive knot, result wrapper, postulate, hole,
--     permissive option, or broad dispatcher import.

open import Coercions using (Coercion; src)
open import Conversion using
  ( conceal-conversion-typing
  ; conversion↑⇒coercion
  ; conversion↓⇒coercion
  ; reveal-conversion-typing
  )
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; sym; trans)
import NarrowWiden as NW
open import NuReduction using (ξ-⟨⟩)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-right-ctx-[]
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; _⟨_⟩
  ; ν
  ; no•-⟨⟩
  ; no•-ν
  ; ok-no
  ; ok-⟨⟩
  ; ok-ν
  )
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢ν↑
  ; ⊢ν⊑
  )
open import Types using (Ty; TyCtx; `∀)
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.DGG.Core.NuPreservation using (value-no-step)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceCastFrameStepDef
  using (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  using (world-coherent-source-one-step-outcome-mapᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPairedCastFrameDef
  using
  ( WorldCoherentSourceOneStepPairedCastFrameᵀ
  ; sourceStepPairedConcealFrame
  ; sourceStepPairedRevealFrame
  ; sourceStepPairedWideningFrame
  )
open import
  proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef
  using (WorldCoherentSourceOneStepPrefixᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepQuotientDownUpStepDef
  using (WorldCoherentSourceOneStepQuotientDownUpStepᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using
  ( WorldCoherentSourceOneStepSourceCastFrames
  ; sourceStepSourceConcealFrame
  ; sourceStepSourceNarrowFrame
  ; sourceStepSourceRevealFrame
  ; sourceStepSourceWidenFrame
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


cast-runtime :
  ∀ {M c} →
  RuntimeOK (M ⟨ c ⟩) →
  RuntimeOK M
cast-runtime (ok-no (no•-⟨⟩ no-M)) = ok-no no-M
cast-runtime (ok-⟨⟩ ok-M) = ok-M


ν-runtime :
  ∀ {A N s} →
  RuntimeOK (ν A N s) →
  RuntimeOK N
ν-runtime (ok-no (no•-ν no-N)) = ok-no no-N
ν-runtime (ok-ν ok-N) = ok-N


cast-body-typing-at :
  ∀ {Δ Σ Γ M c A B} →
  src c ≡ A →
  Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
cast-body-typing-at src≡A (⊢⟨⟩↑ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↑⇒coercion c⊢)))) src≡A) M⊢
cast-body-typing-at src≡A (⊢⟨⟩↓ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↓⇒coercion c⊢)))) src≡A) M⊢
cast-body-typing-at src≡A (⊢⟨⟩⊒ mode seal★ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A) M⊢
cast-body-typing-at src≡A (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A) M⊢


ν-body-typing-at :
  ∀ {Δ Σ Γ A N s B C} →
  src s ≡ C →
  Δ ∣ Σ ∣ Γ ⊢ ν A N s ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ N ⦂ `∀ C
ν-body-typing-at src≡C (⊢ν↑ hA N⊢ s⊢) =
  subst (λ X → _ ∣ _ ∣ _ ⊢ _ ⦂ `∀ X)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↑⇒coercion s⊢)))) src≡C) N⊢
ν-body-typing-at src≡C (⊢ν⊑ mode seal★ N⊢ s⊢) =
  subst (λ X → _ ∣ _ ∣ _ ⊢ _ ⦂ `∀ X)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ s⊢)))) src≡C) N⊢


world-coherent-source-cast-frame-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceOneStepSourceCastFrames →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceOneStepPairedCastFrameᵀ →
  WorldCoherentSourceOneStepQuotientDownUpStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (cast⊒⊑ᵀ mode seal★ c⊒ inner q c-shape comp) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceNarrowFrame source-frames prefixρ
      mode seal★ c⊒ c-shape comp)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c⊒))) source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (cast⊑⊑ᵀ mode seal★ c⊑ inner q c-shape comp) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceWidenFrame source-frames prefixρ
      mode seal★ c⊑ c-shape comp)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c⊑))) source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (conv↑⊑ᵀ c↑ inner q replace) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceRevealFrame source-frames prefixρ c↑ replace)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c↑))))
        source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (conv↓⊑ᵀ c↓ inner q replace) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceConcealFrame source-frames prefixρ c↓ replace)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c↓))))
        source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ inner q c′-shape comp) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNarrowFrame target-frames prefixρ
      mode′ seal★′ c′⊒ c′-shape comp)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊒))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ inner q c′-shape comp) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetWidenFrame target-frames prefixρ
      mode′ seal★′ c′⊑ c′-shape comp)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↑ᵀ c′↑ inner q replace) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetRevealFrame target-frames prefixρ c′↑ replace)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c′↑))))
        target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↓ᵀ c′↓ inner q replace) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetConcealFrame target-frames prefixρ c′↓ replace)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c′↓))))
        target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (paired-revealᵀ corr c↑ c′↑ replacement inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepPairedRevealFrame paired-frame prefixρ
      corr c↑ c′↑ replacement)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) (cast-runtime ok-target)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion
            (reveal-conversion-typing c↑)))) source⊢)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion
            (reveal-conversion-typing c′↑)))) target⊢)
      inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (paired-concealᵀ corr c↓ c′↓ replacement inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepPairedConcealFrame paired-frame prefixρ
      corr c↓ c′↓ replacement)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) (cast-runtime ok-target)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion
            (conceal-conversion-typing c↓)))) source⊢)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion
            (conceal-conversion-typing c′↓)))) target⊢)
      inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp compatible inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepPairedWideningFrame paired-frame prefixρ
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp compatible)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (cast-runtime ok-source) (cast-runtime ok-target)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c⊑))) source⊢)
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (closeᵀ inner widening pA
      source-shape target-shape square compatible) M→M₁ =
  quotient-step prefix prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢ inner widening M→M₁
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames paired-frame quotient-step
    prefixρ coherent
    exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (gen⊑groundᵀ mode seal★ (c⊢ , NW.gen safe)
      gH vV vW W⊢ V⊑Wtag q) M→M₁ =
  ⊥-elim
    (value-no-step vV M→M₁)
