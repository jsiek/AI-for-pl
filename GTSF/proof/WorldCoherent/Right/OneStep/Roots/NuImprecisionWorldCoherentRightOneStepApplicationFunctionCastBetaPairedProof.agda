module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedProof
  where

-- File Charter:
--   * Proves both paired source/target function-cast beta terminals.
--   * Reconstructs the post-beta relation at the final store and packages
--     exactly the source function-cast beta step against the already-reduced
--     target.
--   * Delegates only the two pure quotient-aware application relations.
--   * Contains no recursion, postulate, hole, permissive option, catch-all,
--     or compatibility wrapper.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
import CastImprecisionShape as CastShape
open import ConversionIndexCompatibility using
  (replace-paired-function)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import ImprecisionComposition using
  ( comp-↦-↦
  ; quotient-boundary-square
  ; source-perm-refl
  )
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
open import NuTerms using
  ( No•
  ; Term
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import PairedWideningCompatibility using
  ( compatible-function
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ·⊑·ᵀ
  )
open import
  proof.Core.Properties.TypePreservation
  using (seal★-weaken)
open import
  proof.DGG.Core.NuPreservation
  using
  ( runtime-·₁
  ; value-runtime-No•
  )
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using
  ( quotient-widening-pair-prefix-proofᵀ
  ; store-corresponds-prefix-proofᵀ
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using
  ( quotiented-store-prefix-no-bullet-proofᵀ
  ; quotiented-store-prefix-no-bulletᵖ-proofᵀ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaPairedCastValuesᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientValuesᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues
  )
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma
  using (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepIndexedResult
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  )
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV

  source-result-outcome :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ L : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherentSourceOneStepIndexedResult
      {M = M} {M′ = M′} {L = L}
      {χ = keep} {ρ = ρ} p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p
  source-result-outcome complete =
    world-indexed-outcome-related
      (sourceStepIndexedResult complete)
      (sourceStepStoreLineage complete)
      (sourceStepWorldCoherent complete)
      (sourceStepSourceNameExclusive complete)
      (sourceStepAssumptionMembershipUnique complete)


world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ →
  SourceFunctionCastBetaPairedQuotientRelationᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues
world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ
    function-compatible quotient =
  record
    { rightStepApplicationFunctionCastBetaPairedCastValues =
        paired-cast-values
    ; rightStepApplicationFunctionCastBetaPairedQuotientValues =
        paired-quotient-values
    }
  where
  paired-cast-values :
    WorldCoherentRightOneStepApplicationFunctionCastBetaPairedCastValuesᵀ
  paired-cast-values
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfL okM okM′
      (paired-conversion
        (paired-reveal corresponds
          (CV.reveal-fun c↓ d↑)
          (CV.reveal-fun e↓ f↑)
          (replace-paired-function c-replace d-replace)))
      inner argument-related vV vM vV′ vW′ =
    source-result-outcome
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vM)))
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    corresponds⁺ =
      store-corresponds-prefix-proofᵀ relation-prefix corresponds
    c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
    d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
    e↓⁺ = CV.weaken-conceal-conversion right-incl e↓
    f↑⁺ = CV.weaken-reveal-conversion right-incl f↑
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-V-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-V-no inner
    argument-paired =
      paired-conversion
        (paired-conceal corresponds⁺ c↓⁺ e↓⁺ c-replace)
    argument-cast =
      conv⊑convᵀ argument-paired argument-related
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    result-paired =
      paired-conversion
        (paired-reveal corresponds⁺ d↑⁺ f↑⁺ d-replace)
    final-related =
      conv⊑convᵀ result-paired application-related
  paired-cast-values
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfL okM okM′
      (paired-conversion
        (paired-conceal corresponds
          (CV.conceal-fun c↑ d↓)
          (CV.conceal-fun e↑ f↓)
          (replace-paired-function c-replace d-replace)))
      inner argument-related vV vM vV′ vW′ =
    source-result-outcome
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vM)))
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    corresponds⁺ =
      store-corresponds-prefix-proofᵀ relation-prefix corresponds
    c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
    d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
    e↑⁺ = CV.weaken-reveal-conversion right-incl e↑
    f↓⁺ = CV.weaken-conceal-conversion right-incl f↓
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-V-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-V-no inner
    argument-paired =
      paired-conversion
        (paired-reveal corresponds⁺ c↑⁺ e↑⁺ c-replace)
    argument-cast =
      conv⊑convᵀ argument-paired argument-related
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    result-paired =
      paired-conversion
        (paired-conceal corresponds⁺ d↓⁺ f↓⁺ d-replace)
    final-related =
      conv⊑convᵀ result-paired application-related
  paired-cast-values
      {C = A₀ ⇒ B₀} {C′ = A₀′ ⇒ B₀′}
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfL okM okM′
      (paired-widening
        mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
        (CastShape.shape-fun c-shape d-shape)
        mode′ seal★′
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        (CastShape.shape-fun e-shape f-shape)
        source-comp target-comp
        (compatible-function compatible))
      inner argument-related vV vM vV′ vW′ =
    source-result-outcome
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vM)))
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    seal★′⁺ = seal★-weaken right-incl seal★′
    c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
    d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
    source-widening⁺ =
      C.cast-fun (proj₁ c⊒⁺) (proj₁ d⊑⁺) ,
      NW.cross (cⁿ NW.↦ dʷ)
    e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
    f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
    target-widening⁺ =
      C.cast-fun (proj₁ e⊒⁺) (proj₁ f⊑⁺) ,
      NW.cross (eⁿ NW.↦ fʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-V-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-V-no inner
    final-related =
      function-compatible mode seal★⁺ source-widening⁺
        (CastShape.shape-fun c-shape d-shape)
        mode′ seal★′⁺ target-widening⁺
        (CastShape.shape-fun e-shape f-shape)
        (quotient-boundary-square
          source-perm-refl source-comp
          source-perm-refl target-comp)
        compatible inner⁺ argument-related
  paired-cast-values
      {C = A₀ ⇒ B₀} {C′ = A₀′ ⇒ B₀′}
      {pC = pA₀ ↦ pB₀} {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (paired-widening
        mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
        (CastShape.shape-fun c-shape d-shape)
        mode′ seal★′
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        (CastShape.shape-fun e-shape f-shape)
        source-comp target-comp
        (compatible-target-inert-bridge bridge))
      inner argument-related vV vM vV′ vW′
      with bridge (_ C.↦ _)
  paired-cast-values
      {C = A₀ ⇒ B₀} {C′ = A₀′ ⇒ B₀′}
      {pC = pA₀ ↦ pB₀} {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (paired-widening
        mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
        (CastShape.shape-fun c-shape d-shape)
        mode′ seal★′
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        (CastShape.shape-fun e-shape f-shape)
        source-comp target-comp
        (compatible-target-inert-bridge bridge))
      inner argument-related vV vM vV′ vW′
      | (pA-bridge ↦ pB-bridge)
          , (comp-↦-↦ c-comp d-comp)
          , (comp-↦-↦ e-comp f-comp) =
    source-result-outcome
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vM)))
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    seal★′⁺ = seal★-weaken right-incl seal★′
    c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
    d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
    e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
    f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-V-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-V-no inner
    target-argument-cast =
      ⊑cast⊒ᵀ mode′ seal★′⁺ e⊒⁺ argument-related pA-bridge
        e-shape e-comp
    argument-casts =
      cast⊒⊑ᵀ mode seal★⁺ c⊒⁺ target-argument-cast pA₀
        c-shape c-comp
    application-related = ·⊑·ᵀ inner⁺ argument-casts
    source-result-cast =
      cast⊑⊑ᵀ mode seal★⁺ d⊑⁺ application-related pB-bridge
        d-shape d-comp
    final-related =
      ⊑cast⊑ᵀ mode′ seal★′⁺ f⊑⁺ source-result-cast pB
        f-shape f-comp

  paired-quotient-values :
    WorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientValuesᵀ
  paired-quotient-values
      relation-prefix coherent exclusive unique wfL okM okM′
      inner widening source-shape target-shape square
      argument-related vV vM vV′ vW′ =
    source-result-outcome
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vM)))
    where
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    target-function-no =
      value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-V-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bulletᵖ-proofᵀ
        relation-prefix source-V-no target-V-no inner
    widening⁺ =
      quotient-widening-pair-prefix-proofᵀ relation-prefix widening
    final-related =
      quotient inner⁺ widening⁺ source-shape target-shape square
        argument-related
