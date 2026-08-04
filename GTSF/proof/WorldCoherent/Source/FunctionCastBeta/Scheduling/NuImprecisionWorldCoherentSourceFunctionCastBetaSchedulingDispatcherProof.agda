module
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingDispatcherProof
  where

-- File Charter:
--   * Proves arbitrary-target source function-cast beta scheduling by
--     structural recursion on QTI.
--   * Passes direct target-application outcomes through unchanged and
--     transports recursive outcomes through target casts and conversions
--     without discarding source blame.
--   * Contains no direct coercion algebra, catch-all, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)

open import Coercions using (src)
open import Conversion using
  ( conceal-conversion-typing
  ; conversion↑⇒coercion
  ; conversion↓⇒coercion
  ; reveal-conversion-typing
  )
open import NuTerms using
  ( RuntimeOK
  ; no•-⟨⟩
  ; no•-ν
  ; ok-no
  ; ok-⟨⟩
  ; ok-ν
  ; ν
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( ·⊑·ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceFunctionCastBetaRootᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesDef
  using
  ( WorldCoherentSourceFunctionCastBetaSchedulingCases
  ; sourceFunctionCastBetaDirectCase
  ; sourceFunctionCastBetaTargetBulletCase
  ; sourceFunctionCastBetaTargetCastFrames
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( sourceStepTargetConcealFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  using (world-coherent-source-one-step-outcome-mapᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ)
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


private
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
      (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A)
      M⊢
  cast-body-typing-at src≡A (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
    subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
      (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A)
      M⊢

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
      (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ s⊢)))) src≡C)
      N⊢


world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ :
  WorldCoherentSourceFunctionCastBetaSchedulingCases →
  WorldCoherentSourceFunctionCastBetaRootᵀ
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (·⊑·ᵀ L⊑L′ W⊑R′) vV vW =
  sourceFunctionCastBetaDirectCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ L⊑L′ W⊑R′ vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q c-shape comp) vV vW =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetNarrowFrame target-frames
      prefix mode seal★ c⊒ c-shape comp)
    (λ source↠blame → _ , source↠blame)
    recursive
  where
  target-frames = sourceFunctionCastBetaTargetCastFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (cast-runtime okM′) M⊢
      (cast-body-typing-at (proj₁ (coercion-src-tgtᵐ (proj₁ c⊒)))
        M′⊢)
      inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q c-shape comp) vV vW =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetWidenFrame target-frames
      prefix mode seal★ c⊑ c-shape comp)
    (λ source↠blame → _ , source↠blame)
    recursive
  where
  target-frames = sourceFunctionCastBetaTargetCastFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (cast-runtime okM′) M⊢
      (cast-body-typing-at (proj₁ (coercion-src-tgtᵐ (proj₁ c⊑)))
        M′⊢)
      inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (⊑conv↑ᵀ c↑ inner q replace) vV vW =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetRevealFrame target-frames prefix c↑ replace)
    (λ source↠blame → _ , source↠blame)
    recursive
  where
  target-frames = sourceFunctionCastBetaTargetCastFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (cast-runtime okM′) M⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c↑))))
        M′⊢)
      inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (⊑conv↓ᵀ c↓ inner q replace) vV vW =
  world-coherent-source-one-step-outcome-mapᵀ
    (sourceStepTargetConcealFrame target-frames prefix c↓ replace)
    (λ source↠blame → _ , source↠blame)
    recursive
  where
  target-frames = sourceFunctionCastBetaTargetCastFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (cast-runtime okM′) M⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion (conceal-conversion-typing c↓))))
        M′⊢)
      inner vV vW
