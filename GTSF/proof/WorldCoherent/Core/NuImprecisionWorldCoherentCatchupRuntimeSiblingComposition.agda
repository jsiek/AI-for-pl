module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  where

-- File Charter:
--   * Composes a world-coherent left-silent prefix with a recursively caught
--     result while carrying one independent runtime sibling.
--   * Returns the composed caught result and sibling at its exact final world.
--   * Normalizes nested term, type, and imprecision-index transport directly.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _++_)
open import Data.Product using (_,_; Σ-syntax)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silentᵀ
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; silentIndexedResult
  ; sourceChanges
  ; sourceResult
  ; sourceTypeResult
  ; targetResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTerms-++; applyTys-++)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )


world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ R R′ : Term} {A B C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  (silent : LeftSilentIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  let first =
        weakIndexedResult (silentIndexedResult silent)
  in
  WeakOneStepStoreLineage first →
  (Σ[ second-caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = sourceResult first}
      {V′ = targetResult first}
      {ρ = resultStore first}
      (transportType first p) ]
    let second =
          weakIndexedResult
            (catchupIndexedResult
              (worldCatchupResult second-caught))
    in
    resultCtx second
      ∣ resultLeftCtx second
      ∣ resultRightCtx second
      ∣ resultStore second ∣ []
      ⊢ᴺ applyTerms (sourceChanges second)
          (applyTerms (sourceChanges first) R)
        ⊑ applyTerms (targetTailChanges second)
            (applyTerm keep
              (applyTerms (targetTailChanges first)
                (applyTerm keep R′)))
      ⦂ applyTys (sourceChanges second)
          (applyTys (sourceChanges first) C)
        ⊑ applyTys (targetTailChanges second)
            (applyTy keep
              (applyTys (targetTailChanges first)
                (applyTy keep C′)))
      ∶ transportType second (transportType first q)) →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = M} {V′ = V′} {ρ = ρ} p ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result)
            (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) C
        ⊑ applyTys (targetTailChanges result)
            (applyTy keep C′)
      ∶ transportType result q
world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    {R = R} {A = A} {B = B} {C = C}
    {p = p} {q = q}
    silent@(left-silent-indexed first-indexed
      (left-silent-invariant refl refl) first-runtime)
    first-lineage
    (second-caught@(world-coherent-left-indexed-catchup
      second-catchup@(left-indexed-catchup second-indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      second-lineage coherent exclusive unique wfL) ,
      second-sibling) =
  caught , combined-sibling
  where
  first-raw = weakIndexedResult first-indexed

  first =
    weak-one-step-reindexᵀ first-raw refl refl
      (canonicalIndexedResults first-indexed)

  first-transport =
    weak-one-step-reindex-preserves-transportᵀ
      first-raw refl refl
      (canonicalIndexedResults first-indexed)
      (weakIndexedTransport first-indexed)

  first-coherence =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      first-raw refl refl
      (canonicalIndexedResults first-indexed)
      (weakIndexedTypeCoherence first-indexed)

  second = weakIndexedResult second-indexed

  raw-combined =
    weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl))
      second

  primary-source-eq :
    applyTys (sourceChanges second) (resultSourceType first) ≡
      applyTys
        (sourceChanges first ++ sourceChanges second) A
  primary-source-eq =
    trans
      (cong (applyTys (sourceChanges second))
        (sourceTypeResult first))
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) A))

  primary-target-eq :
    applyTys (targetTailChanges second)
        (applyTy keep (resultTargetType first)) ≡
      applyTys (targetTailChanges second) (applyTy keep B)
  primary-target-eq =
    cong
      (λ T → applyTys (targetTailChanges second)
        (applyTy keep T))
      (targetTypeResult first)

  primary-index-eq =
    HE.≅-to-≡
      (HE.trans
        (subst²-to-≅
          {P = λ S T → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑ T ⊣ resultRightCtx second}
          primary-source-eq primary-target-eq
          (transportType second (transportType first p)))
        (HE.sym
          (weak-one-step-compose-type-to-nested≅
            first second p)))

  canonical =
    nu-term-imprecision-transport-typesᵀ
      primary-source-eq primary-target-eq primary-index-eq
      (canonicalIndexedResults second-indexed)

  combined =
    weak-one-step-reindexᵀ
      raw-combined refl refl canonical

  raw-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl))
      second first-transport
      (weakIndexedTransport second-indexed)

  combined-transport =
    weak-one-step-reindex-preserves-transportᵀ
      raw-combined refl refl canonical raw-transport

  raw-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl))
      second first-coherence
      (weakIndexedTypeCoherence second-indexed)

  combined-coherence =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      raw-combined refl refl canonical raw-coherence

  combined-indexed =
    weak-indexed-result
      combined canonical combined-transport combined-coherence

  combined-catchup =
    left-indexed-catchup combined-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)

  first-lineage′ =
    weak-step-store-lineage
      (lineageStore first-lineage)
      (lineageEmbedding first-lineage)
      (lineagePrefix first-lineage)

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first (left-silent-invariant refl refl))
      second first-lineage′ second-lineage

  caught =
    world-coherent-left-indexed-catchup
      combined-catchup
      (weak-step-store-lineage
        (lineageStore combined-lineage)
        (lineageEmbedding combined-lineage)
        (lineagePrefix combined-lineage))
      coherent exclusive unique wfL

  source-term-eq =
    sym (applyTerms-++
      (sourceChanges first) (sourceChanges second) R)

  source-type-eq =
    sym (applyTys-++
      (sourceChanges first) (sourceChanges second) C)

  sibling-index-eq =
    HE.≅-to-≡
      (HE.trans
        (subst²-to-≅
          {P = λ S T → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑ T ⊣ resultRightCtx second}
          source-type-eq refl
          (transportType second (transportType first q)))
        (HE.sym
          (weak-one-step-compose-type-to-nested≅
            first second q)))

  combined-sibling =
    nu-term-imprecision-transport-termsᵀ
      source-term-eq refl
      (nu-term-imprecision-transport-typesᵀ
        source-type-eq refl sibling-index-eq second-sibling)
