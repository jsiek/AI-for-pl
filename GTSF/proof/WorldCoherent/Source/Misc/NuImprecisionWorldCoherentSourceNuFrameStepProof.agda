module proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepProof where

-- File Charter:
--   * Proves the higher-order fit of source `ν` congruence against every
--     quotiented term-imprecision constructor that can expose a source `ν`.
--   * Recurses only through the supplied source-step prefix capability and
--     maps its existing flat outcome through the frozen exact `ν` frames.
--   * Contains no canonical recursive knot, result carrier, wrapper,
--     postulate, hole, permissive option, or broad dispatcher import.

open import Coercions using (src)
open import Conversion using
  ( conceal-conversion-typing
  ; conversion↑⇒coercion
  ; conversion↓⇒coercion
  ; reveal-conversion-typing
  )
open import Data.Product using (_,_; proj₁)
open import NuReduction using (ξ-ν)
open import NuTermImprecision using (lift-right-ctx-[])
open import NuTerms using
  ( RuntimeOK
  ; _⟨_⟩
  ; ν
  ; no•-⟨⟩
  ; no•-ν
  ; ok-no
  ; ok-⟨⟩
  ; ok-ν
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; sym; trans)
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢ν↑
  ; ⊢ν⊑
  )
open import Types using (`∀)
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (ν-blame-tailᵀ)
open import proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepDef using
  (WorldCoherentSourceNuFrameStepᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  using (world-coherent-source-one-step-outcome-mapᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef
  using (WorldCoherentSourceOneStepPrefixᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  using
  ( WorldCoherentSourceOneStepSourceNuFrames
  ; sourceStepMatchedNuFrame
  ; sourceStepSourceNuFrame
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetBulletFrameStepDef
  using (WorldCoherentSourceOneStepTargetBulletFrameStepᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )


ν-runtime :
  ∀ {A N s} →
  RuntimeOK (ν A N s) →
  RuntimeOK N
ν-runtime (ok-no (no•-ν no-N)) = ok-no no-N
ν-runtime (ok-ν ok-N) = ok-N


cast-runtime :
  ∀ {M c} →
  RuntimeOK (M ⟨ c ⟩) →
  RuntimeOK M
cast-runtime (ok-no (no•-⟨⟩ no-M)) = ok-no no-M
cast-runtime (ok-⟨⟩ ok-M) = ok-M


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


world-coherent-source-ν-frame-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceOneStepSourceNuFrames →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceOneStepTargetBulletFrameStepᵀ →
  WorldCoherentSourceNuFrameStepᵀ
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (allocation-prefixᵀ prefix₀ inner inner-source⊢ inner-target⊢)
    N→N′ =
  prefix (store-imp-prefix-transⁱ prefix₀ prefixρ)
    coherent exclusive unique wfL wfR ok-source ok-target source⊢ target⊢
    inner (ξ-ν N→N′)
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
      liftρ liftγ inner paired-replace)
    N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepMatchedNuFrame source-ν-frames
      {pA = A⊑A′} {A⇑⊑A′⇑ = A⇑⊑A′⇑}
      prefixρ s↑ s′↑ paired-replace)
    (λ source↠blame → _ , ν-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (ν-runtime ok-source) (ν-runtime ok-target)
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s↑))))
        source⊢)
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s′↑))))
        target⊢)
      inner N→N′)
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ inner replace) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceNuFrame source-ν-frames prefixρ hA s↑ replace)
    (λ source↠blame → _ , ν-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR
      (ν-runtime ok-source) ok-target
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s↑))))
        source⊢)
      target⊢ inner N→N′)
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ inner q c-shape comp) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNarrowFrame target-cast-frames prefixρ
      mode′ seal★′ c′⊒ c-shape comp)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊒))) target⊢)
      inner (ξ-ν N→N′))
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ inner q c-shape comp) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetWidenFrame target-cast-frames prefixρ
      mode′ seal★′ c′⊑ c-shape comp)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner (ξ-ν N→N′))
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑idᵀ seal★′ c′⊑ inner q c-shape comp) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetIdWidenFrame target-cast-frames prefixρ
      seal★′ c′⊑ c-shape comp)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner (ξ-ν N→N′))
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↑ᵀ c′↑ inner q replace) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetRevealFrame target-cast-frames prefixρ c′↑ replace)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c′↑))))
        target⊢)
      inner (ξ-ν N→N′))
world-coherent-source-ν-frame-step-proofᵀ
    prefix source-ν-frames target-cast-frames
    target-bullet-step prefixρ coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↓ᵀ c′↓ inner q replace) N→N′ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetConcealFrame target-cast-frames prefixρ c′↓ replace)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive unique wfL wfR ok-source
      (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c′↓))))
        target⊢)
      inner (ξ-ν N→N′))
