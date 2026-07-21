module proof.NuImprecisionWorldCoherentSourceCastFrameStepProof where

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
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; sym; trans)
open import NuReduction using (ξ-⟨⟩)
open import NuTermImprecision using
  (StoreImp; lift-right-ctx-[])
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
  ( PairedCast
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; up⊑upᵀ
  ; ⊑αᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
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
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import
  proof.NuImprecisionWorldCoherentSourceCastFrameStepDef
  using (WorldCoherentSourceCastFrameStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  using (world-coherent-source-one-step-outcome-mapᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepPairedCastFrameDef
  using (WorldCoherentSourceOneStepPairedCastFrameᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef
  using (WorldCoherentSourceOneStepPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepQuotientDownUpStepDef
  using (WorldCoherentSourceOneStepQuotientDownUpStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using
  ( WorldCoherentSourceOneStepSourceCastFrames
  ; sourceStepSourceConcealFrame
  ; sourceStepSourceNarrowFrame
  ; sourceStepSourceRevealFrame
  ; sourceStepSourceWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetBulletFrameStepDef
  using (WorldCoherentSourceOneStepTargetBulletFrameStepᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using
  ( WorldCoherentSourceOneStepTargetNuFrames
  ; sourceStepTargetNuCastFrame
  ; sourceStepTargetNuFrame
  )
open import proof.NuImprecisionTargetBlameCatchup using
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


paired-source-src :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  src c ≡ A
paired-source-src
    (paired-conversion (paired-reveal x∈ c↑ c′↑)) =
  proj₁ (coercion-src-tgtᵐ
    (conversion↑⇒coercion (reveal-conversion-typing c↑)))
paired-source-src
    (paired-conversion (paired-conceal x∈ c↓ c′↓)) =
  proj₁ (coercion-src-tgtᵐ
    (conversion↓⇒coercion (conceal-conversion-typing c↓)))
paired-source-src
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat) =
  proj₁ (coercion-src-tgtᵐ (proj₁ c⊑))


paired-target-src :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  src c′ ≡ A′
paired-target-src
    (paired-conversion (paired-reveal x∈ c↑ c′↑)) =
  proj₁ (coercion-src-tgtᵐ
    (conversion↑⇒coercion (reveal-conversion-typing c′↑)))
paired-target-src
    (paired-conversion (paired-conceal x∈ c↓ c′↓)) =
  proj₁ (coercion-src-tgtᵐ
    (conversion↓⇒coercion (conceal-conversion-typing c′↓)))
paired-target-src
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat) =
  proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))


world-coherent-source-cast-frame-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceOneStepSourceCastFrames →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceOneStepTargetNuFrames →
  WorldCoherentSourceOneStepPairedCastFrameᵀ →
  WorldCoherentSourceOneStepQuotientDownUpStepᵀ →
  WorldCoherentSourceOneStepTargetBulletFrameStepᵀ →
  WorldCoherentSourceCastFrameStepᵀ
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (allocation-prefixᵀ prefix₀ inner inner-source⊢ inner-target⊢)
    M→M₁ =
  prefix (store-imp-prefix-transⁱ prefix₀ prefixρ)
    coherent exclusive wfL wfR ok-source ok-target source⊢ target⊢
    inner (ξ-⟨⟩ M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (cast⊒⊑ᵀ mode seal★ c⊒ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceNarrowFrame source-frames prefixρ
      mode seal★ c⊒)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c⊒))) source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (cast⊑⊑ᵀ mode seal★ c⊑ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceWidenFrame source-frames prefixρ
      mode seal★ c⊑)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c⊑))) source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (conv↑⊑ᵀ c↑ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceRevealFrame source-frames prefixρ c↑)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c↑))))
        source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (conv↓⊑ᵀ c↓ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepSourceConcealFrame source-frames prefixρ c↓)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR
      (cast-runtime ok-source) ok-target
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c↓))))
        source⊢)
      target⊢ inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNarrowFrame target-frames prefixρ
      mode′ seal★′ c′⊒)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊒))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetWidenFrame target-frames prefixρ
      mode′ seal★′ c′⊑)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑idᵀ seal★′ c′⊑ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetIdWidenFrame target-frames prefixρ
      seal★′ c′⊑)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↑ᵀ c′↑ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetRevealFrame target-frames prefixρ c′↑)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c′↑))))
        target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↓ᵀ c′↓ inner q) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetConcealFrame target-frames prefixρ c′↓)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (cast-runtime ok-target)
      source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c′↓))))
        target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (conv⊑convᵀ paired inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (paired-frame prefixρ paired)
    (λ source↠blame → _ , cast-blame-tailᵀ source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR
      (cast-runtime ok-source) (cast-runtime ok-target)
      (cast-body-typing-at (paired-source-src paired) source⊢)
      (cast-body-typing-at (paired-target-src paired) target⊢)
      inner M→M₁)
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (up⊑upᵀ inner widening q) M→M₁ =
  quotient-step prefix prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢ inner widening M→M₁
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ r inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNuFrame target-ν-frames prefixρ hA s↑ r)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (ν-runtime ok-target)
      source⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s↑))))
        target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ r inner) M→M₁ =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNuCastFrame target-ν-frames prefixρ
      mode seal★ s⊑ r)
    (λ source↠blame → _ , source↠blame)
    (prefix prefixρ coherent exclusive wfL wfR ok-source
      (ν-runtime ok-target)
      source⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ s⊑))) target⊢)
      inner (ξ-⟨⟩ M→M₁))
world-coherent-source-cast-frame-step-proofᵀ
    prefix source-frames target-frames target-ν-frames paired-frame
    quotient-step target-bullet-step prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑αᵀ vL′ noL′ h⇑A liftρ lift-right-ctx-[] inner r
      inner-source⊢ inner-target⊢)
    M→M₁ =
  target-bullet-step prefix h⇑A prefixρ coherent exclusive wfL wfR
    ok-source ok-target source⊢ target⊢ vL′ noL′ liftρ inner
    inner-source⊢ inner-target⊢ (ξ-⟨⟩ M→M₁)
