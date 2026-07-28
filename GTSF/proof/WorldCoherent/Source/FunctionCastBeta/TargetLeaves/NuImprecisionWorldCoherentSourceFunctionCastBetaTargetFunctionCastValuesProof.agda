module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesProof
  where

-- File Charter:
--   * Proves the positive-rank target-function-cast value terminal by
--     exhaustive inversion of the function relation.
--   * Peels one target function cast before invoking the lower-rank
--     target-value scheduler; paired beta leaves remain explicit parameters.
--   * Contains no catch-all, postulate, hole, termination pragma, or
--     permissive option.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (shape-fun)
open import ConversionIndexCompatibility using
  (replace-left-function; replace-right-function)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl; suc-injective)
open import Data.Product using (_,_)

open import ImprecisionComposition using (comp-↦-↦)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (β-↦; keep; pure-step)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; ok-·₂
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; _⇒_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bullet-proofᵀ)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  ( WorldCoherentSourceFunctionCastBetaPairedValues
  ; sourceFunctionCastBetaPairedConcealValuesCase
  ; sourceFunctionCastBetaPairedQuotientValuesCase
  ; sourceFunctionCastBetaPairedRevealValuesCase
  ; sourceFunctionCastBetaPairedWideningValuesCase
  )
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueRankedDef
  using
  ( WorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesAtᵀ
  ; WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ
  )
open import proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using
  ( WorldCoherentSourceOneStepOutcome
  ; source-step-outcome-related
  )
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  using (world-coherent-source-one-step-outcome-mapᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependDef
  using (WorldCoherentSourceTargetKeepPrependᵀ)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-·₂; runtime-⟨⟩; value-runtime-No•)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


target-function-cast-values-suc-at-prefixᵀ :
  ∀ {n} →
  WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n →
  WorldCoherentSourceFunctionCastBetaPairedValues →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceTargetKeepPrependᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ} {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((L′ ⟨ e C.↦ f ⟩) · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  (vL′ : Value L′) →
  Value R′ →
  suc (targetFunctionCastSpineRank vL′) ≡ suc n →
  WorldCoherentSourceOneStepOutcome
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = (L′ ⟨ e C.↦ f ⟩) · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (allocation-prefixᵀ prefix₀ inner source⊢ target⊢)
    argument-related vV vW vL′ vR′ outer-rank =
  target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    (store-imp-prefix-transⁱ prefix₀ relation-prefix)
    coherent exclusive unique wfL wfR okM okM′ inner
    argument-related vV vW vL′ vR′ outer-rank
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (cast⊒⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cʷ NW.↦ dⁿ))
      inner .(pA ↦ pB)
      (shape-fun c-shape d-shape)
      (comp-↦-↦ c-comp d-comp))
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  c⊑⁺ = NW.widen-weaken ≤-refl left-incl (c⊢ , cʷ)
  d⊒⁺ = NW.narrow-weaken ≤-refl left-incl (d⊢ , dⁿ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    cast⊑⊑ᵀ mode seal★⁺ c⊑⁺ argument-related pA₀
      c-shape c-comp
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    cast⊒⊑ᵀ mode seal★⁺ d⊒⁺ application-related pB
      d-shape d-comp
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (cast⊑⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      inner .(pA ↦ pB)
      (shape-fun c-shape d-shape)
      (comp-↦-↦ c-comp d-comp))
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    cast⊒⊑ᵀ mode seal★⁺ c⊒⁺ argument-related pA₀
      c-shape c-comp
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    cast⊑⊑ᵀ mode seal★⁺ d⊑⁺ application-related pB
      d-shape d-comp
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (conv↑⊑ᵀ {p = pA₀ ↦ pB₀}
      (CV.reveal-fun c↓ d↑) inner .(pA ↦ pB)
      (replace-left-function c-replace d-replace))
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
  d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    conv↓⊑ᵀ c↓⁺ argument-related pA₀ c-replace
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    conv↑⊑ᵀ d↑⁺ application-related pB d-replace
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (conv↓⊑ᵀ {p = pA₀ ↦ pB₀}
      (CV.conceal-fun c↑ d↓) inner .(pA ↦ pB)
      (replace-left-function c-replace d-replace))
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
  d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    conv↑⊑ᵀ c↑⁺ argument-related pA₀ c-replace
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    conv↓⊑ᵀ d↓⁺ application-related pB d-replace
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (closeᵀ inner widening p source-shape target-shape square compatible)
    argument-related vV vW vL′ vR′ outer-rank =
  sourceFunctionCastBetaPairedQuotientValuesCase paired
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    inner widening source-shape target-shape square
    compatible
    argument-related vV vW vL′ vR′
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (paired-revealᵀ corresponds source target replacement inner)
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (sourceFunctionCastBetaPairedRevealValuesCase paired
      relation-prefix coherent exclusive unique wfR okM okM′
      corresponds source target replacement inner
      argument-related vV vW vL′ vR′)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (paired-concealᵀ corresponds source target replacement inner)
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (sourceFunctionCastBetaPairedConcealValuesCase paired
      relation-prefix coherent exclusive unique wfR okM okM′
      corresponds source target replacement inner
      argument-related vV vW vL′ vR′)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (paired-wideningᵀ {p = pA₀ ↦ pB₀}
      mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      (shape-fun c-shape d-shape)
      mode′ seal★′
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
      (shape-fun e-shape f-shape)
      source-comp target-comp compatible inner)
    argument-related vV vW vL′ vR′ outer-rank =
  source-step-outcome-related
    (sourceFunctionCastBetaPairedWideningValuesCase paired
      relation-prefix coherent exclusive unique wfR okM okM′
      mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      (shape-fun c-shape d-shape)
      mode′ seal★′
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
      (shape-fun e-shape f-shape)
      source-comp target-comp compatible inner
      argument-related vV vW vL′ vR′)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (⊑cast⊒ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun e⊢ f⊢ , NW.cross (eʷ NW.↦ fⁿ))
      inner .(pA ↦ pB)
      (shape-fun e-shape f-shape)
      (comp-↦-↦ e-comp f-comp))
    argument-related vV vW vL′ vR′ outer-rank =
  world-coherent-source-one-step-outcome-mapᵀ
    (λ result →
      prepend (pure-step (β-↦ vL′ vR′))
        (sourceStepTargetNarrowFrame target-frames
          prefix-reflⁱ mode seal★⁺ f⊒⁺ f-shape f-comp result))
    (λ source↠blame → _ , source↠blame)
    inner-result
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken right-incl seal★
  e⊑⁺ = NW.widen-weaken ≤-refl right-incl (e⊢ , eʷ)
  f⊒⁺ = NW.narrow-weaken ≤-refl right-incl (f⊢ , fⁿ)
  source-function-value = vV ⟨ _ C.↦ _ ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  target-L-no =
    value-runtime-No• vL′ (runtime-⟨⟩ (runtime-·₁ okM′))
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑cast⊑ᵀ mode seal★⁺ e⊑⁺ argument-related pA₀
      e-shape e-comp
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-function-no target-L-no inner
  inner-result =
    lower prefix-reflⁱ coherent exclusive unique wfL wfR okM
      (ok-·₂ vL′ target-L-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW vL′
      (suc-injective outer-rank)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (⊑cast⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
      inner .(pA ↦ pB)
      (shape-fun e-shape f-shape)
      (comp-↦-↦ e-comp f-comp))
    argument-related vV vW vL′ vR′ outer-rank =
  world-coherent-source-one-step-outcome-mapᵀ
    (λ result →
      prepend (pure-step (β-↦ vL′ vR′))
        (sourceStepTargetWidenFrame target-frames
          prefix-reflⁱ mode seal★⁺ f⊑⁺ f-shape f-comp result))
    (λ source↠blame → _ , source↠blame)
    inner-result
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken right-incl seal★
  e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
  f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
  source-function-value = vV ⟨ _ C.↦ _ ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  target-L-no =
    value-runtime-No• vL′ (runtime-⟨⟩ (runtime-·₁ okM′))
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑cast⊒ᵀ mode seal★⁺ e⊒⁺ argument-related pA₀
      e-shape e-comp
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-function-no target-L-no inner
  inner-result =
    lower prefix-reflⁱ coherent exclusive unique wfL wfR okM
      (ok-·₂ vL′ target-L-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW vL′
      (suc-injective outer-rank)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (⊑conv↑ᵀ {p = pA₀ ↦ pB₀}
      (CV.reveal-fun e↓ f↑) inner .(pA ↦ pB)
      (replace-right-function e-replace f-replace))
    argument-related vV vW vL′ vR′ outer-rank =
  world-coherent-source-one-step-outcome-mapᵀ
    (λ result →
      prepend (pure-step (β-↦ vL′ vR′))
        (sourceStepTargetRevealFrame target-frames
          prefix-reflⁱ f↑⁺ f-replace result))
    (λ source↠blame → _ , source↠blame)
    inner-result
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  e↓⁺ = CV.weaken-conceal-conversion right-incl e↓
  f↑⁺ = CV.weaken-reveal-conversion right-incl f↑
  source-function-value = vV ⟨ _ C.↦ _ ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  target-L-no =
    value-runtime-No• vL′ (runtime-⟨⟩ (runtime-·₁ okM′))
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑conv↓ᵀ e↓⁺ argument-related pA₀ e-replace
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-function-no target-L-no inner
  inner-result =
    lower prefix-reflⁱ coherent exclusive unique wfL wfR okM
      (ok-·₂ vL′ target-L-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW vL′
      (suc-injective outer-rank)
target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL wfR okM okM′
    (⊑conv↓ᵀ {p = pA₀ ↦ pB₀}
      (CV.conceal-fun e↑ f↓) inner .(pA ↦ pB)
      (replace-right-function e-replace f-replace))
    argument-related vV vW vL′ vR′ outer-rank =
  world-coherent-source-one-step-outcome-mapᵀ
    (λ result →
      prepend (pure-step (β-↦ vL′ vR′))
        (sourceStepTargetConcealFrame target-frames
          prefix-reflⁱ f↓⁺ f-replace result))
    (λ source↠blame → _ , source↠blame)
    inner-result
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  e↑⁺ = CV.weaken-reveal-conversion right-incl e↑
  f↓⁺ = CV.weaken-conceal-conversion right-incl f↓
  source-function-value = vV ⟨ _ C.↦ _ ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  target-L-no =
    value-runtime-No• vL′ (runtime-⟨⟩ (runtime-·₁ okM′))
  target-function-value = vL′ ⟨ _ C.↦ _ ⟩
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑conv↑ᵀ e↑⁺ argument-related pA₀ e-replace
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-function-no target-L-no inner
  inner-result =
    lower prefix-reflⁱ coherent exclusive unique wfL wfR okM
      (ok-·₂ vL′ target-L-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW vL′
      (suc-injective outer-rank)


world-coherent-source-function-cast-beta-target-function-cast-values-suc-at-proofᵀ :
  ∀ {n} →
  WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n →
  WorldCoherentSourceFunctionCastBetaPairedValues →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceTargetKeepPrependᵀ →
  WorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesAtᵀ
    (suc n)
world-coherent-source-function-cast-beta-target-function-cast-values-suc-at-proofᵀ
    lower paired target-frames prepend
    coherent exclusive unique wfL wfR okM okM′
    function-related argument-related vV vW vL′ vR′ outer-rank =
  target-function-cast-values-suc-at-prefixᵀ
    lower paired target-frames prepend prefix-reflⁱ
    coherent exclusive unique wfL wfR okM okM′
    function-related argument-related vV vW vL′ vR′ outer-rank
