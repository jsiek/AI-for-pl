module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Proves exact-final paired-cast catch-up with one independent runtime
--     sibling.
--   * Keeps conversion, source blame, and hereditary source-inert completion
--     store-neutral.
--   * Delegates the isolated source-value paired-conversion family through its
--     exact-final runtime-sibling contract.
--   * Delegates the allocation-sensitive compatible-widening branch to the
--     source-widen sibling field and its exact silent-resumption join before
--     adding the inert target frame.
--   * Contains no allocation recovery, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Coercions as C
open import NuReduction using
  ( blame-⟨⟩
  ; pure-step
  )
open import NuTerms using
  ( no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  ( compatible-all
  ; compatible-function
  ; compatible-gen
  ; compatible-source-leaf
  ; compatible-target-inert-bridge
  ; inert-leaf
  )
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-target-typing
  ; paired-conversion
  ; paired-widening
  ; prefix-reflⁱ
  )
open import
  proof.Catchup.Core.NuImprecisionCatchupComposition
  using (left-catchup-indexed-prepend-keepᵀ)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixSupport
  using
  ( left-catchup-indexed-prefix-blameᵀ
  ; left-catchup-indexed-prefix-valueᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
  )
open import
  proof.Quotient.NuImprecisionQuotientValue
  using (left-catchup-indexed-one-keep-valueᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames
  using (world-coherent-left-catchup-prefix-target-widen-castᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-coherent-left-indexed-catchup)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupDef
  using (WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupDef
  using
  (WorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeSiblingCatchupDef
  using
  ( WorldCoherentSourceRuntimeSiblingCatchupᵀ
  ; source-widen-sibling
  )
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ :
  WorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupᵀ →
  WorldCoherentSourceRuntimeSiblingCatchupᵀ →
  WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL (inj₂ refl)
    vV′ noV′ inert-c′
    paired W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  target⊢ = nu-term-imprecision-target-typing
    (conv⊑convᵀ paired W⊑V′)

  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prepend-keepᵀ
        (pure-step blame-⟨⟩)
        (left-catchup-indexed-prefix-blameᵀ
          prefix-reflⁱ (no•-⟨⟩ noV′)
          (blame⊑ᵀ target⊢)))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-conversion conversion)
    W⊑V′ noR okR′ sibling =
  conversion-catchup
    coherent exclusive unique wfL
    vW noW vV′ noV′ inert-c′ conversion
    W⊑V′ noR okR′ sibling
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    paired@(paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-source-leaf leaf))
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ inert-leaf leaf ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ paired W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    paired@(paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-function {c₁ = c₁} {c₂ = c₂} residual))
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ c₁ C.↦ c₂ ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ paired W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    paired@(paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-all {c = c} residual))
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ C.`∀ c ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ paired W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    paired@(paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-gen {A = A} {c = c} residual))
    W⊑V′ noR okR′ sibling =
  caught , sibling
  where
  caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-valueᵀ
        prefix-reflⁱ (ok-no (no•-⟨⟩ noW))
        (vW ⟨ C.gen A c ⟩) (no•-⟨⟩ noV′)
        (conv⊑convᵀ paired W⊑V′))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-target-inert-bridge bridge-evidence))
    W⊑V′ noR okR′ sibling
    with bridge-evidence inert-c′
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-target-inert-bridge bridge-evidence))
    W⊑V′ noR okR′ sibling
    | bridge , source-triangle , target-triangle
    with
      source-widen-sibling source-runtime
        prefix-reflⁱ mode seal★ c⊑
        vV′ noV′ noR okR′
        (world-coherent-left-indexed-catchup
          (left-catchup-indexed-prefix-valueᵀ
            prefix-reflⁱ (ok-no noW) vW noV′ W⊑V′)
          (weak-step-store-lineage
            _ rel-store-embedding-reflⁱ prefix-reflⁱ)
          coherent exclusive unique wfL)
        sibling
        bridge c-shape source-triangle
world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    conversion-catchup source-runtime
    coherent exclusive unique wfL
    (inj₁ (vW , noW)) vV′ noV′ inert-c′
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp
      (compatible-target-inert-bridge bridge-evidence))
    W⊑V′ noR okR′ sibling
    | bridge , source-triangle , target-triangle
    | inner@(world-coherent-left-indexed-catchup
        (left-indexed-catchup _
          (left-catchup-invariant
            (left-silent-invariant refl refl) _))
        _ _ _ _ _) ,
      inner-sibling =
  framed , inner-sibling
  where
  framed =
    world-coherent-left-catchup-prefix-target-widen-castᵀ
      prefix-reflⁱ mode′ seal★′ c′⊑ c′-shape
      target-triangle inner
