module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupProof
  where

-- File Charter:
--   * Composes left value catch-up with synchronized matched-`ν` allocation.
--   * Returns one indexed result together with lineage for that exact result.
--   * Takes the base matched-allocation step as a dependency and contains no
--     dispatcher, postulate, hole, permissive option, or legacy allocation
--     simulation import.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (Coercion)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  )
open import NuReduction using (applyTys; bind; keep)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Relation.Binary.HeterogeneousEquality as HE
open import Types using
  ( Ty
  ; TyCtx
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-indexed-all-resultᵀ
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-matched-ν-frame-preserves-transportᵀ
  ; weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-ν-frameᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silentᵀ
  ; weak-result-source-reveal
  ; weak-result-target-reveal
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( weak-one-step-index-resultᵀ
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  )
open import proof.Core.Equality.HeterogeneousEqualityTransport using
  ( subst²-to-≅
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
  ( replace-paired-transport-endpoints
  ; transport-imprecision-endpoints
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTysUnderTyBinders-⇑ᵗ)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (∀ᵢᶜ; ⊑-lift∀ᵢ)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupDef
  using (MatchedNuAllocationAfterValueCatchupᵀ)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepDef
  using (MatchedNuAllocationStepᵀ)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-store-embeddingⁱ)
open import QuotientedTermImprecision using
  (prefix-reflⁱ; prefix-∷ⁱ)


matched-nu-allocation-after-value-catchup-proofᵀ :
  MatchedNuAllocationStepᵀ →
  MatchedNuAllocationAfterValueCatchupᵀ
matched-nu-allocation-after-value-catchup-proofᵀ
    step {A = A} {A′ = A′}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
    catchup@(left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW lineage =
  final-indexed ,
  proj₁ (lift-store-result (resultStore inner)) ,
  ⇑ᵗ (applyTys (sourceChanges inner) A) ,
  ⇑ᵗ (applyTys (keep ∷ targetTailChanges inner) A′) ,
  transported-A ,
  final-lineage ,
  liftρ₀ ,
  second-store
  where
  old-catchup = left-all-catchup
    (weak-indexed-all-resultᵀ indexed)
    (catchupIndexedAllInvariant catchup)

  inner-coherence = weakIndexedTypeCoherence indexed
  inner = weakResult (catchupAllResult old-catchup)
  innerAll = canonicalAllResults (catchupAllResult old-catchup)
  first = weak-one-step-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (catchupAllResult old-catchup) inner-coherence
  silent-first = left-silent first (left-silent-invariant refl refl)
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source↑ = proj₂ (weak-result-source-reveal inner s↑)
  target↑ = proj₂ (weak-result-target-reveal keep inner s′↑)
  source-A-eq =
    applyTysUnderTyBinders-⇑ᵗ (sourceChanges inner) A
  target-A-eq =
    applyTysUnderTyBinders-⇑ᵗ
      (keep ∷ targetTailChanges inner) A′
  transported-A =
    transport-imprecision-endpoints source-A-eq target-A-eq
      (transportAllBody inner A⇑⊑A′⇑)
  transported-replace =
    replace-paired-transport-endpoints
      refl refl refl refl source-A-eq target-A-eq
      (transportAllBodyPairedReplacementCoherent
        inner-coherence replace)

  second-pair = step
    vW noW vV′ noV′ source↑ target↑
    (transportType inner pB)
    transported-A transported-replace liftρ₀ innerAll
  second-indexed = proj₁ second-pair
  second-raw = weakIndexedResult second-indexed
  second = weak-one-step-reindexᵀ second-raw refl refl
    (canonicalIndexedResults second-indexed)
  second-transport =
    weak-one-step-reindex-preserves-transportᵀ
      second-raw refl refl
      (canonicalIndexedResults second-indexed)
      (weakIndexedTransport second-indexed)
  second-coherence =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      second-raw refl refl
      (canonicalIndexedResults second-indexed)
      (weakIndexedTypeCoherence second-indexed)
  second-lineage = proj₁ (proj₂ second-pair)
  second-store = proj₁ (proj₂ (proj₂ second-pair))

  result = weak-one-step-prepend-left-silentᵀ silent-first second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx result ∣ resultLeftCtx result
          ⊢ S ⊑ T ⊣ resultRightCtx result}
        (sourceTypeResult result)
        (targetTypeResult result)
        (resultType result))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second pB)))

  transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      silent-first
      second
      (weak-one-step-matched-ν-frame-preserves-transportᵀ
        s↑ s′↑ pA A⇑⊑A′⇑ pB replace
        (catchupAllResult old-catchup) inner-coherence
        (weakIndexedTransport indexed))
      second-transport

  coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      silent-first
      second
      (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
        s↑ s′↑ pA A⇑⊑A′⇑ pB replace
        (catchupAllResult old-catchup) inner-coherence)
      second-coherence

  final-indexed =
    weak-one-step-index-resultᵀ result type-eq transport coherence

  final-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      silent-first
      second
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      (weak-step-store-lineage
        (lineageStore second-lineage)
        (lineageEmbedding second-lineage)
        (lineagePrefix second-lineage))
