module proof.NuImprecisionWorldCoherentSourceNuCatchupProof where

-- File Charter:
--   * Implements accumulated-world ordinary source-only `ν` catch-up.
--   * Frames the completed operand catch-up, transports its reveal conversion
--     to the final world, and delegates allocation to the exact-final contract.
--   * Propagates source blame and composes explicit relational-store lineage.
--   * Contains no canonical assembly, recursive dispatcher, or permissive
--     option.

open import Agda.Builtin.Equality using (refl)
open import Conversion using
  (weaken-reveal-conversion)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import NuReduction using
  (applyTys; blame-ν)
open import NuStore using (StoreIncl-cons)
open import NuTermImprecision using
  (leftStoreⁱ; lift-left-ctx-[])
open import NuTerms using
  (no•-blame; ok-no; ok-ν)
open import QuotientedTermImprecision using
  (blame⊑ᵀ; nu-term-imprecision-target-typing; prefix-reflⁱ)
open import Types using (WfTy; ⇑ᵗ)
open import proof.MediationProperties using (wfTy-applyTys)
open import proof.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.NuImprecisionCatchupSourceAllocationTerminal using
  (left-silent-indexed-prefix-source-ν-terminal-valueᵀ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.NuImprecisionSimulationCore using
  ( weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-ν-frameᵀ
  ; weak-result-source-all
  ; weak-result-source-reveal
  )
open import proof.NuImprecisionSimulationResultDef using
  ( catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; weak-indexed-result
  ; weakIndexedResult
  )
open import proof.NuImprecisionStoreLift using
  (lift-left-store-result)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.NuImprecisionWorldCoherentFinalSourceNuCatchupDef using
  (WorldCoherentFinalSourceNuCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import proof.NuImprecisionWorldCoherentSourceNuCatchupDef using
  (WorldCoherentSourceNuCatchupᵀ)
open import proof.StoreProperties using (renameStoreᵗ-incl)
open import proof.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)


world-coherent-source-ν-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCatchupᵀ →
  WorldCoherentSourceNuCatchupᵀ
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    with final
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    with weak-result-source-reveal
      (weakIndexedResult indexed)
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        c↑)
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    | μ′ , final-reveal
    with weak-result-source-all (weakIndexedResult indexed)
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    | μ′ , final-reveal
    | q′ , W⊑V′
    with lift-left-store-result (resultStore (weakIndexedResult indexed))
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    | μ′ , final-reveal
    | q′ , W⊑V′
    | final-store , final-lift =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent first-lineage
    (final-catchup coherent exclusive wfL final-wf final-shift-wf
      final-reveal final-lift lift-left-ctx-[]
      vW noW vV′ noV′ W⊑V′)
  where
  inner = weakIndexedResult indexed

  first-lineage =
    weak-step-store-lineage
      (lineageStore inner-lineage)
      (lineageEmbedding inner-lineage)
      (lineagePrefix inner-lineage)

  final-wf =
    subst
      (λ Δ → WfTy Δ (applyTys (sourceChanges inner) _))
      (sym (sourceCtxResult inner))
      (wfTy-applyTys (sourceChanges inner) hA)

  final-shift-wf =
    renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

  first-silent =
    left-silent-indexed-prefix-source-ν-terminal-valueᵀ
      prefix hA c↑ catchup vW noW
world-coherent-source-ν-catchup-proofᵀ
    final-catchup prefix hA h⇑A c↑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      inner-lineage coherent exclusive wfL)
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent first-lineage terminal
  where
  inner = weakIndexedResult indexed

  first-lineage =
    weak-step-store-lineage
      (lineageStore inner-lineage)
      (lineageEmbedding inner-lineage)
      (lineagePrefix inner-lineage)

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  c↑⁺ = weaken-reveal-conversion source-store-incl c↑

  framed = weak-one-step-source-ν-frameᵀ hA c↑⁺ _ inner

  first-silent =
    left-silent-indexed
      (weak-indexed-result framed (relatedResults framed))
      (left-silent-invariant refl refl)
      (ok-ν (ok-no no•-blame))
      (weak-one-step-source-ν-frame-preserves-transportᵀ
        hA c↑⁺ _ inner inner-transport)
      (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
        hA c↑⁺ _ inner inner-coherence)

  target⊒ =
    nu-term-imprecision-target-typing (relatedResults framed)

  second-relation = blame⊑ᵀ target⊒

  second = weak-one-step-keep-source-catchupᵀ
    blame-ν second-relation

  terminal =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup
        (weak-indexed-result second (relatedResults second))
        (left-catchup-invariant
          (left-silent-invariant refl refl) (inj₂ refl))
        (weak-one-step-keep-source-catchup-transportᵀ
          blame-ν second-relation)
        (weak-one-step-keep-source-catchup-type-coherenceᵀ
          blame-ν second-relation))
      (weak-step-store-lineage
        (resultStore framed) rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive wfL
