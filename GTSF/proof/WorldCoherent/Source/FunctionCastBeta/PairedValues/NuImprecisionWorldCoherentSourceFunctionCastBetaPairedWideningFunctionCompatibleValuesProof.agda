module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesProof
  where

-- File Charter:
--   * Proves the world-coherent function-compatible paired-widening beta leaf
--     from its pure beta-distributed term-imprecision relation.
--   * Handles store-prefix weakening and synchronizes both beta steps.
--   * Contains no semantic relation implementation, postulate, hole,
--     catch-all, or permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)

open import ImprecisionComposition using
  (quotient-boundary-square; source-perm-refl)
open import NuReduction using (β-↦; pure-step)
open import NuTerms using
  (No•; no•-⟨⟩; _⟨_⟩)
open import proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ)
open import proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)
open import proof.DGG.Core.NuPreservation using
  (value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-·₁)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
import NarrowWiden as NW


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


world-coherent-source-function-cast-beta-paired-widening-function-compatible-values-proofᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-function-compatible-values-proofᵀ
    relation relation-prefix coherent exclusive unique wfR okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    source-shape
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    target-shape source-comp target-comp
    compatible inner argument-related vV vW vL′ vR′ =
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
    value-runtime-No• (vL′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-L-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-L-no inner
  final-related =
    relation mode seal★⁺ source-widening⁺ source-shape
      mode′ seal★′⁺ target-widening⁺ target-shape
      (quotient-boundary-square
        source-perm-refl source-comp
        source-perm-refl target-comp)
      compatible inner⁺ argument-related
