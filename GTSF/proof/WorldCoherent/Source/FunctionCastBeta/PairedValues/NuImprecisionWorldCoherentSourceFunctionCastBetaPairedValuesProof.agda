module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesProof
  where

-- File Charter:
--   * Assembles the paired value leaves by proving both paired-conversion
--     function cases and delegating only paired widening and quotient
--     widening.
--   * Builds the distributed argument/result relations at the ambient store
--     and synchronizes the two function-cast beta steps.
--   * Contains no catch-all, postulate, hole, or permissive option.

import Coercions as C
import Conversion as CV

open import ConversionIndexCompatibility using
  (replace-paired-function)
open import ImprecisionWf using (_↦_)
open import NuReduction using (β-↦; pure-step)
open import NuTerms using
  (No•; no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; ·⊑·ᵀ
  )
open import Types using (_⇒_)
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  (store-corresponds-prefix-proofᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  ( WorldCoherentSourceFunctionCastBetaPairedCastValuesᵀ
  ; WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
  ; WorldCoherentSourceFunctionCastBetaPairedValues
  ; sourceFunctionCastBetaPairedCastValuesCase
  ; sourceFunctionCastBetaPairedQuotientValuesCase
  )
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-⟨⟩; value-runtime-No•)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV

  paired-cast-values :
    WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ →
    WorldCoherentSourceFunctionCastBetaPairedCastValuesᵀ
  paired-cast-values widening
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfR okM okM′
      (paired-conversion
        (paired-reveal corresponds
          (CV.reveal-fun c↓ d↑)
          (CV.reveal-fun e↓ f↑)
          (replace-paired-function c-replace d-replace)))
      inner argument-related vV vW vL′ vR′ =
    world-coherent-source-target-keep-prependᵀ
      (pure-step (β-↦ vL′ vR′))
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vW)))
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
      value-runtime-No• (vL′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-L-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-L-no inner
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
  paired-cast-values widening
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfR okM okM′
      (paired-conversion
        (paired-conceal corresponds
          (CV.conceal-fun c↑ d↓)
          (CV.conceal-fun e↑ f↓)
          (replace-paired-function c-replace d-replace)))
      inner argument-related vV vW vL′ vR′ =
    world-coherent-source-target-keep-prependᵀ
      (pure-step (β-↦ vL′ vR′))
      (world-coherent-source-keep-relationᵀ
        coherent exclusive unique final-related
        (pure-step (β-↦ vV vW)))
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
      value-runtime-No• (vL′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
    target-L-no = cast-value-body-No• target-function-no
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-L-no inner
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
  paired-cast-values widening
      {C = A₀ ⇒ B₀} {C′ = A₀′ ⇒ B₀′}
      {pC = pA₀ ↦ pB₀}
      relation-prefix coherent exclusive unique wfR okM okM′
      (paired-widening
        mode seal★ source-widening source-shape
        mode′ seal★′ target-widening target-shape
        source-comp target-comp compatible)
      inner argument-related vV vW vL′ vR′ =
    widening relation-prefix coherent exclusive unique wfR okM okM′
      mode seal★ source-widening source-shape
      mode′ seal★′ target-widening target-shape
      source-comp target-comp
      compatible inner argument-related vV vW vL′ vR′


world-coherent-source-function-cast-beta-paired-values-proofᵀ :
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedValues
world-coherent-source-function-cast-beta-paired-values-proofᵀ
    widening quotient =
  record
    { sourceFunctionCastBetaPairedCastValuesCase =
        paired-cast-values widening
    ; sourceFunctionCastBetaPairedQuotientValuesCase = quotient
    }
