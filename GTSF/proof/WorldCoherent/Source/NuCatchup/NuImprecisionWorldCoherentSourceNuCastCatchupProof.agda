module proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCastCatchupProof where

-- File Charter:
--   * Implements accumulated-world source-only runtime `ν ★` catch-up.
--   * Frames the completed operand catch-up, transports its instantiation
--     cast to the final world, and delegates fresh allocation to the exact-
--     final source-`ν ★` contract.
--   * Propagates source blame and composes explicit relational-store lineage.
--   * Contains no canonical mutual assembly or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions using (instᵈ)
open import NarrowWiden using (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (applyTyCtxs; applyTys; blame-ν)
open import NuStore using (StoreIncl-cons)
open import NuTermImprecision using (leftStoreⁱ)
open import NuTerms using
  (no•-blame; ok-no; ok-ν)
open import QuotientedTermImprecision using
  (blame⊑ᵀ; nu-term-imprecision-target-typing; prefix-reflⁱ)
open import TermTyping using (SealModeStore★)
open import Types using (★; ⇑ᵗ; ⟰ᵗ)
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.Catchup.Core.NuImprecisionCatchupSourceAllocationTerminal using
  (left-silent-indexed-prefix-source-νcast-terminal-valueᵀ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-widen-inst-under-ty-binders
  ; weak-one-step-source-νcast-frame-preserves-transportᵀ
  ; weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-νcast-frameᵀ
  ; weak-result-source-all
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef using
  (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCastCatchupDef using
  (WorldCoherentSourceNuCastCatchupᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyTysUnderTyBinders
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


world-coherent-source-νcast-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentSourceNuCastCatchupᵀ
world-coherent-source-νcast-catchup-proofᵀ
    final-catchup prefix mode seal★ c⊑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive wfL)
    with final
world-coherent-source-νcast-catchup-proofᵀ
    final-catchup prefix mode seal★ c⊑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        seal★)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        c⊑)
world-coherent-source-νcast-catchup-proofᵀ
    final-catchup prefix mode seal★ c⊑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    | μ′ , mode′ , final-seal₀ , final-cast₀
    with weak-result-source-all (weakIndexedResult indexed)
world-coherent-source-νcast-catchup-proofᵀ
    final-catchup prefix mode seal★ c⊑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive wfL)
    | inj₁ (vW , noW)
    | μ′ , mode′ , final-seal₀ , final-cast₀
    | q′ , W⊑V′ =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent first-lineage
    (final-catchup coherent exclusive wfL mode′ final-seal final-cast
      vW noW vV′ noV′ W⊑V′)
  where
  inner = weakIndexedResult indexed

  first-lineage =
    weak-step-store-lineage
      (lineageStore inner-lineage)
      (lineageEmbedding inner-lineage)
      (lineagePrefix inner-lineage)

  final-seal =
    subst
      (λ Σ → SealModeStore★ (instᵈ μ′)
        ((zero , ★) ∷ ⟰ᵗ Σ))
      (sym (sourceStoreResult inner)) final-seal₀

  final-cast =
    subst
      (λ Δ → instᵈ μ′ ∣ suc Δ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
        ⊢ applyCoercionUnderTyBinders (sourceChanges inner) _
          ∶ applyTysUnderTyBinders (sourceChanges inner) _
            ⊑ ⇑ᵗ (applyTys (sourceChanges inner) _))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → instᵈ μ′
          ∣ suc (applyTyCtxs (sourceChanges inner) _)
          ∣ (zero , ★) ∷ ⟰ᵗ Σ
          ⊢ applyCoercionUnderTyBinders (sourceChanges inner) _
            ∶ applyTysUnderTyBinders (sourceChanges inner) _
              ⊑ ⇑ᵗ (applyTys (sourceChanges inner) _))
        (sym (sourceStoreResult inner)) final-cast₀)

  first-silent =
    left-silent-indexed-prefix-source-νcast-terminal-valueᵀ
      prefix mode seal★ c⊑ catchup vW noW
world-coherent-source-νcast-catchup-proofᵀ
    final-catchup prefix mode seal★ c⊑ liftρ liftγ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
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

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊑⁺ = widen-weaken ≤-refl source-store-incl c⊑

  framed =
    weak-one-step-source-νcast-frameᵀ
      mode seal★⁺ c⊑⁺ _ indexed

  first-silent =
    left-silent-indexed
      (weak-indexed-result framed (relatedResults framed)
        (weak-one-step-source-νcast-frame-preserves-transportᵀ
          mode seal★⁺ c⊑⁺ _ indexed (weakIndexedTransport indexed))
        (weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
          mode seal★⁺ c⊑⁺ _ indexed (weakIndexedTypeCoherence indexed)))
      (left-silent-invariant refl refl)
      (ok-ν (ok-no no•-blame))

  target⊒ =
    nu-term-imprecision-target-typing (relatedResults framed)

  second-relation = blame⊑ᵀ target⊒

  second = weak-one-step-keep-source-catchupᵀ
    blame-ν second-relation

  terminal =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup
        (weak-indexed-result second (relatedResults second)
          (weak-one-step-keep-source-catchup-transportᵀ
            blame-ν second-relation)
          (weak-one-step-keep-source-catchup-type-coherenceᵀ
            blame-ν second-relation))
        (left-catchup-invariant
          (left-silent-invariant refl refl) (inj₂ refl)))
      (weak-step-store-lineage
        (resultStore framed) rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive wfL
