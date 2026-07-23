module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingDispatcherProof
  where

-- File Charter:
--   * Proves arbitrary-target source function-cast beta scheduling by
--     structural recursion on QTI.
--   * Delegates direct target applications and transports completed results
--     through target bullets, casts, conversions, and `ν` frames.
--   * Contains no direct coercion algebra, catch-all, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (proj₁)
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
  ( allocation-prefixᵀ
  ; ·⊑·ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
  )
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceFunctionCastBetaRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesDef
  using
  ( WorldCoherentSourceFunctionCastBetaSchedulingCases
  ; sourceFunctionCastBetaDirectCase
  ; sourceFunctionCastBetaTargetBulletCase
  ; sourceFunctionCastBetaTargetCastFrames
  ; sourceFunctionCastBetaTargetNuFrames
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using
  ( sourceStepTargetNuCastFrame
  ; sourceStepTargetNuFrame
  )
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
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
    M⊢ M′⊢ (allocation-prefixᵀ prefix₀ inner M⊢₀ M′⊢₀) vV vW =
  world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfL wfR okM okM′ M⊢ M′⊢ inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢
    relation@(⊑αᵀ vL′ noL′ hA liftρ liftγ inner
      r N⊢ L′•⊢) vV vW =
  sourceFunctionCastBetaTargetBulletCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ relation vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (⊑νᵀ hA h⇑A s↑ liftρ liftγ r inner) vV vW =
  sourceStepTargetNuFrame target-ν-frames prefix hA s↑ r recursive
  where
  target-ν-frames = sourceFunctionCastBetaTargetNuFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (ν-runtime okM′) M⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s↑))))
        M′⊢)
      inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ r inner) vV vW =
  sourceStepTargetNuCastFrame target-ν-frames
    prefix mode seal★ s⊑ r recursive
  where
  target-ν-frames = sourceFunctionCastBetaTargetNuFrames cases
  recursive =
    world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
      cases prefix coherent exclusive unique wfL wfR okM
      (ν-runtime okM′) M⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ s⊑))) M′⊢)
      inner vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (·⊑·ᵀ L⊑L′ W⊑R′) vV vW =
  sourceFunctionCastBetaDirectCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ L⊑L′ W⊑R′ vV vW
world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ (⊑cast⊒ᵀ mode seal★ c⊒ inner q) vV vW =
  sourceStepTargetNarrowFrame target-frames
    prefix mode seal★ c⊒ recursive
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
    M⊢ M′⊢ (⊑cast⊑ᵀ mode seal★ c⊑ inner q) vV vW =
  sourceStepTargetWidenFrame target-frames
    prefix mode seal★ c⊑ recursive
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
    M⊢ M′⊢ (⊑cast⊑idᵀ seal★ c⊑ inner q) vV vW =
  sourceStepTargetIdWidenFrame target-frames
    prefix seal★ c⊑ recursive
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
    M⊢ M′⊢ (⊑conv↑ᵀ c↑ inner q) vV vW =
  sourceStepTargetRevealFrame target-frames prefix c↑ recursive
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
    M⊢ M′⊢ (⊑conv↓ᵀ c↓ inner q) vV vW =
  sourceStepTargetConcealFrame target-frames prefix c↓ recursive
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
