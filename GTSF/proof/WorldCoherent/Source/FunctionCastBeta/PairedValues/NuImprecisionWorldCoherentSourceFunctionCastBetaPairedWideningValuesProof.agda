module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesProof
  where

-- File Charter:
--   * Proves paired-widening function beta when compatibility supplies the
--     component bridge.
--   * Delegates only the source-inert compatibility alternative, whose
--     component casts require quotient-aware application distribution.
--   * Contains no catch-all, postulate, hole, or permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
import NarrowWiden as NW
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)

open import Coercions using (_↦_)
open import ImprecisionComposition using (comp-↦-↦)
open import ImprecisionWf using (_↦_)
open import NuReduction using (β-↦; pure-step)
open import NuTerms using
  (No•; no•-⟨⟩; _⟨_⟩)
open import PairedWideningCompatibility using
  ( compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ·⊑·ᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; value-runtime-No•)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ :
  WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ
    source-inert relation-prefix coherent exclusive unique wfR okM okM′
    mode seal★ source-widening source-shape
    mode′ seal★′ target-widening target-shape
    source-comp target-comp
    (compatible-source-inert inert)
    inner argument-related vV vW vL′ vR′ =
  source-inert relation-prefix coherent exclusive unique wfR okM okM′
    mode seal★ source-widening source-shape
    mode′ seal★′ target-widening target-shape
    source-comp target-comp inert
    inner argument-related vV vW vL′ vR′
world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ
    source-inert {pA₀ = pA₀} {pB₀ = pB₀}
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfR okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    source-comp target-comp
    (compatible-target-inert-bridge bridge)
    inner argument-related vV vW vL′ vR′
    with bridge (_ C.↦ _)
world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ
    source-inert {pA₀ = pA₀} {pB₀ = pB₀}
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfR okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    source-comp target-comp
    (compatible-target-inert-bridge bridge)
    inner argument-related vV vW vL′ vR′
    | (pA-bridge ↦ pB-bridge)
        , (comp-↦-↦ c-comp d-comp)
        , (comp-↦-↦ e-comp f-comp) =
  world-coherent-source-target-keep-prependᵀ
    (pure-step (β-↦ vL′ vR′))
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vW)))
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
    value-runtime-No• (vL′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-L-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-L-no inner
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
