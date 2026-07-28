module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesProof
  where

-- File Charter:
--   * Proves the target function-cast beta matrix for a source function-cast
--     value and value arguments.
--   * Recurses only through source-only function casts, terminates paired
--     casts directly, and distributes target-only casts with zero source
--     steps.
--   * Retains exact QTI shapes, composition evidence, store prefixes, and
--     relational-store lineage.
--   * Contains no recursive definition, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (shape-fun)
open import ConversionIndexCompatibility using
  ( replace-left-function
  ; replace-right-function
  )
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionComposition using (comp-↦-↦)
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( β-↦
  ; keep
  ; pure-step
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-·
  ; no•-⟨⟩
  ; ok-no
  ; _·_
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  ( compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; prefix-reflⁱ
  ; up⊑upᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import NuStore using (StoreWf)
open import TermTyping using
  ( SealModeStore★
  ; cast-tag-or-id
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.DGG.Core.NuPreservation using
  ( runtime-·₁
  ; runtime-·₂
  ; runtime-⟨⟩
  ; value-runtime-No•
  )
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-relatedᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef
  using (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentSourceKeepOutcomeComposition
  using (world-coherent-source-keep-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  using
  ( WorldCoherentRightOneStepSourceCastFrames
  ; rightStepSourceNarrowFrame
  ; rightStepSourceWidenFrame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  using
  ( WorldCoherentRightOneStepSourceConversionFrames
  ; rightStepSourceConcealFrame
  ; rightStepSourceRevealFrame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues
  ; rightStepApplicationFunctionCastBetaPairedCastValues
  ; rightStepApplicationFunctionCastBetaPairedQuotientValues
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesAtᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
  )


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV

  related-outcome :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p
  related-outcome coherent exclusive unique relation =
    world-indexed-outcome-related
      (weak-one-step-indexed-relatedᵀ relation)
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique


world-coherent-right-one-step-application-function-cast-beta-function-cast-values-at-proofᵀ :
  ∀ {n} →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
  WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
    n →
  WorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesAtᵀ n
world-coherent-right-one-step-application-function-cast-beta-function-cast-values-at-proofᵀ
    {n} cast-frames conversion-frames paired recursive =
  at-prefix prefix-reflⁱ
  where
  at-prefix :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {V M V′ W′ : Term} {c d e f : C.Coercion}
      {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    StoreImpPrefix ρᵇ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
    RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ V′ ⟨ e C.↦ f ⟩
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
    (vV : Value V) →
    Value M →
    Value V′ →
    Value W′ →
    targetFunctionCastSpineRank vV ≡ n →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (V ⟨ c C.↦ d ⟩) · M}
      {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
      {χ = keep} {ρ = ρ} pB
  at-prefix relation-prefix coherent exclusive unique wfL okM okM′
      (allocation-prefixᵀ prefix₀ inner source⊢ target⊢)
      argument-related vV vM vV′ vW′ rank =
    at-prefix
      (store-imp-prefix-transⁱ prefix₀ relation-prefix)
      coherent exclusive unique wfL okM okM′ inner
      argument-related vV vM vV′ vW′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (cast⊒⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cʷ NW.↦ dⁿ))
        inner .(pA ↦ pB)
        (shape-fun c-shape d-shape)
        (comp-↦-↦ c-comp d-comp))
      argument-related vV vM vV′ vW′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vM))
      (rightStepSourceNarrowFrame cast-frames
        mode seal★⁺ d⊒⁺ d-shape d-comp recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    c⊑⁺ = NW.widen-weaken ≤-refl left-incl (c⊢ , cʷ)
    d⊒⁺ = NW.narrow-weaken ≤-refl left-incl (d⊢ , dⁿ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-M-no =
      value-runtime-No• vM
        (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
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
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-M-no))
    final-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· source-V-no (no•-⟨⟩ source-M-no)))
    recursive-outcome =
      recursive coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ vW′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (cast⊑⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
        inner .(pA ↦ pB)
        (shape-fun c-shape d-shape)
        (comp-↦-↦ c-comp d-comp))
      argument-related vV vM vV′ vW′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vM))
      (rightStepSourceWidenFrame cast-frames
        mode seal★⁺ d⊑⁺ d-shape d-comp recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
    d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-M-no =
      value-runtime-No• vM
        (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
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
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-M-no))
    final-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· source-V-no (no•-⟨⟩ source-M-no)))
    recursive-outcome =
      recursive coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ vW′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (conv↑⊑ᵀ {p = pA₀ ↦ pB₀}
        (CV.reveal-fun c↓ d↑) inner .(pA ↦ pB)
        (replace-left-function c-replace d-replace))
      argument-related vV vM vV′ vW′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vM))
      (rightStepSourceRevealFrame conversion-frames
        d↑⁺ d-replace recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
    d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-M-no =
      value-runtime-No• vM
        (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      conv↓⊑ᵀ c↓⁺ argument-related pA₀ c-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      conv↑⊑ᵀ d↑⁺ application-related pB d-replace
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-M-no))
    final-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· source-V-no (no•-⟨⟩ source-M-no)))
    recursive-outcome =
      recursive coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ vW′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (conv↓⊑ᵀ {p = pA₀ ↦ pB₀}
        (CV.conceal-fun c↑ d↓) inner .(pA ↦ pB)
        (replace-left-function c-replace d-replace))
      argument-related vV vM vV′ vW′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vM))
      (rightStepSourceConcealFrame conversion-frames
        d↓⁺ d-replace recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
    d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-M-no =
      value-runtime-No• vM
        (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      conv↑⊑ᵀ c↑⁺ argument-related pA₀ c-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      conv↓⊑ᵀ d↓⁺ application-related pB d-replace
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-M-no))
    final-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· source-V-no (no•-⟨⟩ source-M-no)))
    recursive-outcome =
      recursive coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ vW′ rank
  at-prefix relation-prefix coherent exclusive unique wfL okM okM′
      (up⊑upᵀ inner widening p source-shape target-shape square)
      argument-related vV vM vV′ vW′ rank =
    rightStepApplicationFunctionCastBetaPairedQuotientValues paired
      relation-prefix coherent exclusive unique wfL okM okM′
      inner widening source-shape target-shape square
      argument-related vV vM vV′ vW′
  at-prefix relation-prefix coherent exclusive unique wfL okM okM′
      (conv⊑convᵀ paired-cast inner)
      argument-related vV vM vV′ vW′ rank =
    rightStepApplicationFunctionCastBetaPairedCastValues paired
      relation-prefix coherent exclusive unique wfL okM okM′
      paired-cast inner argument-related vV vM vV′ vW′
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑cast⊒ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun e⊢ f⊢ , NW.cross (eʷ NW.↦ fⁿ))
        inner .(pA ↦ pB)
        (shape-fun e-shape f-shape)
        (comp-↦-↦ e-comp f-comp))
      argument-related vV vM vV′ vW′ rank =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken right-incl seal★
    e⊑⁺ = NW.widen-weaken ≤-refl right-incl (e⊢ , eʷ)
    f⊒⁺ = NW.narrow-weaken ≤-refl right-incl (f⊢ , fⁿ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑cast⊑ᵀ mode seal★⁺ e⊑⁺ argument-related pA₀
        e-shape e-comp
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      ⊑cast⊒ᵀ mode seal★⁺ f⊒⁺ application-related pB
        f-shape f-comp
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑cast⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        inner .(pA ↦ pB)
        (shape-fun e-shape f-shape)
        (comp-↦-↦ e-comp f-comp))
      argument-related vV vM vV′ vW′ rank =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken right-incl seal★
    e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
    f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑cast⊒ᵀ mode seal★⁺ e⊒⁺ argument-related pA₀
        e-shape e-comp
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      ⊑cast⊑ᵀ mode seal★⁺ f⊑⁺ application-related pB
        f-shape f-comp
  at-prefix
      {ρ = ρ} {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑cast⊑idᵀ {p = pA₀ ↦ pB₀} seal★
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        inner .(pA ↦ pB)
        (shape-fun e-shape f-shape)
        (comp-↦-↦ e-comp f-comp))
      argument-related vV vM vV′ vW′ rank =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ : SealModeStore★ C.id-onlyᵈ (rightStoreⁱ ρ)
    seal★⁺ =
      seal★-weaken {μ = C.id-onlyᵈ} right-incl seal★
    e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
    f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
        (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ e⊒⁺)
        argument-related pA₀ e-shape e-comp
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      ⊑cast⊑idᵀ seal★⁺ f⊑⁺ application-related pB
        f-shape f-comp
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑conv↑ᵀ {p = pA₀ ↦ pB₀}
        (CV.reveal-fun e↓ f↑) inner .(pA ↦ pB)
        (replace-right-function e-replace f-replace))
      argument-related vV vM vV′ vW′ rank =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    e↓⁺ = CV.weaken-conceal-conversion right-incl e↓
    f↑⁺ = CV.weaken-reveal-conversion right-incl f↑
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑conv↓ᵀ e↓⁺ argument-related pA₀ e-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      ⊑conv↑ᵀ f↑⁺ application-related pB f-replace
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑conv↓ᵀ {p = pA₀ ↦ pB₀}
        (CV.conceal-fun e↑ f↓) inner .(pA ↦ pB)
        (replace-right-function e-replace f-replace))
      argument-related vV vM vV′ vW′ rank =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    e↑⁺ = CV.weaken-reveal-conversion right-incl e↑
    f↓⁺ = CV.weaken-conceal-conversion right-incl f↓
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑conv↑ᵀ e↑⁺ argument-related pA₀ e-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      ⊑conv↓ᵀ f↓⁺ application-related pB f-replace
