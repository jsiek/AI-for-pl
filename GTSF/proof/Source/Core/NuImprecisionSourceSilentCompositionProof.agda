module proof.Source.Core.NuImprecisionSourceSilentCompositionProof where

-- File Charter:
--   * Implements source-silent composition for weak one-step results.
--   * Composes generic transport, arrow/`∀` coherence, and relational-store
--     lineage across an already completed target catch-up.
--   * Contains no recursive simulation dispatcher or syntax-specific case.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Imprecision using (NonVar; _ˣ⊑★; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (⌊_⌋; ∀ˢ_; νˢ-injective)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; _↦_
  ; _ˣ⊑ˣ_
  ; ∀ⁱ_
  ; ν
  ; ⇑ᵢ
  )
open import ConversionIndexCompatibility
open import NuReduction using
  ( applyStore
  ; applyStores
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (occurs; ⇑ᵗ; _⇒_; `∀)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( ∀ᵢᶜ
  ; ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  )
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
  ( replace-left-source-shape
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-evidence-shape
  ; replace-paired-source-shape
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  ; transport-imprecision-endpoints
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  using (rel-store-embedding-prefix-invⁱ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.Catchup.Simulation.NuImprecisionIndexedIdentityTransport
  using
  ( transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  ; weak-one-step-nested-source-nu≅
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transportSourceNuType-to-raw≅
  ; transportType-source-subst-to-raw≅
  )
open import proof.Core.Equality.HeterogeneousEqualityTransport using
  ( subst-to-≅
  ; subst²-to-≅
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Source.Core.NuImprecisionSourceSilentCompositionDef
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Core.Properties.ReductionProperties using
  ( applyStores-++
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTyUnderTyBinder
  ; applyTyVar
  ; applyTyVars
  ; applyTy-∀
  ; applyTyCtxs-++
  ; applyTys-++
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTysUnderTyBinders-⇑ᵗ
  ; applyTyVars-++
  ; ↠-trans
  )


source-silent-compose-type :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep) →
  sourceChanges first ≡ [] →
  (second : WeakOneStepResult
    (resultStore first)
    (sourceResult first)
    (targetResult first)
    (resultSourceType first)
    (resultTargetType first)
    keep) →
  ∀ {C D} →
  Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
  resultCtx second ∣ resultLeftCtx second
    ⊢ applyTys (sourceChanges second) C
      ⊑ applyTys
          (targetTailChanges first ++ targetTailChanges second) D
      ⊣ resultRightCtx second
source-silent-compose-type first refl second {C = C} {D = D} p =
  subst
    (λ T → resultCtx second ∣ resultLeftCtx second
      ⊢ applyTys (sourceChanges second) C ⊑ T
      ⊣ resultRightCtx second)
    (sym (applyTys-++
      (targetTailChanges first) (targetTailChanges second) D))
    (transportType second (transportType first p))


source-silent-compose-all-body :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep) →
  sourceChanges first ≡ [] →
  (second : WeakOneStepResult
    (resultStore first)
    (sourceResult first)
    (targetResult first)
    (resultSourceType first)
    (resultTargetType first)
    keep) →
  ∀ {C D} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
    ⊢ applyTysUnderTyBinders (sourceChanges second) C
      ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++ targetTailChanges second) D
      ⊣ suc (resultRightCtx second)
source-silent-compose-all-body first refl second {C = C} {D = D} p =
  subst
    (λ T → ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
      ⊢ applyTysUnderTyBinders (sourceChanges second) C ⊑ T
      ⊣ suc (resultRightCtx second))
    (sym (applyTysUnderTyBinders-++
      (targetTailChanges first) (targetTailChanges second) D))
    (transportAllBody second (transportAllBody first p))


source-silent-compose-right-body :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep) →
  sourceChanges first ≡ [] →
  (second : WeakOneStepResult
    (resultStore first)
    (sourceResult first)
    (targetResult first)
    (resultSourceType first)
    (resultTargetType first)
    keep) →
  ∀ {C D} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
    ⊢ applyTys (sourceChanges second) C
      ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++ targetTailChanges second) D
      ⊣ suc (resultRightCtx second)
source-silent-compose-right-body
    first refl second {C = C} {D = D} p =
  subst
    (λ T → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
      ⊢ applyTys (sourceChanges second) C ⊑ T
      ⊣ suc (resultRightCtx second))
    (sym (applyTysUnderTyBinders-++
      (targetTailChanges first) (targetTailChanges second) D))
    (transportRightBody second (transportRightBody first p))

source-silent-compose-type-to-nested≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep)
    {C D}
    (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  HE._≅_
    (source-silent-compose-type first source-empty second p)
    (transportType second (transportType first p))
source-silent-compose-type-to-nested≅
    first refl second {D = D} p =
  subst-to-≅
    (sym (applyTys-++
      (targetTailChanges first) (targetTailChanges second) D))
    (transportType second (transportType first p))

source-silent-compose-source-nu :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep)
    {C D}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  SourceNuIndex
    (subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑ applyTys
            (targetTailChanges first ++ targetTailChanges second) D
          ⊣ resultRightCtx second)
      (applyTys-∀ (sourceChanges second) C)
      (source-silent-compose-type
        first source-empty second (ν safe occ q)))
source-silent-compose-source-nu
    first refl second {C = C} {D = D} safe occ q =
  sourceNuIndex-reindex (sym combined-eq) transported-shape
  where
  first-shape = transportSourceNu first safe occ q

  second-shape = transportSourceNu second
    (sourceNuSafe first-shape)
    (sourceNuOccurs first-shape)
    (sourceNuBody first-shape)

  target-eq = applyTys-++
    (targetTailChanges first) (targetTailChanges second) D

  transported-shape =
    sourceNuIndex-transport refl (sym target-eq) second-shape

  combined-eq =
    HE.≅-to-≡
      (HE.trans
        (subst-to-≅
          {P = λ S → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑
                applyTys
                  (targetTailChanges first ++
                    targetTailChanges second) D
              ⊣ resultRightCtx second}
          (applyTys-∀ (sourceChanges second) C)
          (source-silent-compose-type
            first refl second (ν safe occ q)))
        (HE.trans
          (source-silent-compose-type-to-nested≅
            first refl second (ν safe occ q))
          (HE.trans
            (weak-one-step-nested-source-nu≅
              first second safe occ q)
            (HE.sym
              (subst²-to-≅
                {P = λ S T → resultCtx second
                  ∣ resultLeftCtx second
                  ⊢ S ⊑ T ⊣ resultRightCtx second}
                refl (sym target-eq)
                (transportSourceNuType second
                  (sourceNuSafe first-shape)
                  (sourceNuOccurs first-shape)
                  (sourceNuBody first-shape)))))))


source-silent-resultᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep) →
  sourceChanges first ≡ [] →
  sourceResult first ≡ M →
  (second : WeakOneStepResult
    (resultStore first)
    (sourceResult first)
    (targetResult first)
    (resultSourceType first)
    (resultTargetType first)
    keep) →
  WeakOneStepResult ρ M M′ A B keep
source-silent-resultᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    first refl refl second =
  record
    { sourceChanges = sourceChanges second
    ; targetTailChanges =
        targetTailChanges first ++ targetTailChanges second
    ; sourceResult = sourceResult second
    ; targetResult = targetResult second
    ; resultCtx = resultCtx second
    ; resultLeftCtx = resultLeftCtx second
    ; resultRightCtx = resultRightCtx second
    ; sourceCtxResult =
        trans (sourceCtxResult second)
          (cong (applyTyCtxs (sourceChanges second))
            (sourceCtxResult first))
    ; targetCtxResult =
        trans (targetCtxResult second)
          (trans
            (cong (applyTyCtxs (targetTailChanges second))
              (targetCtxResult first))
            (sym (applyTyCtxs-++
              (targetTailChanges first)
              (targetTailChanges second) Δᴿ)))
    ; resultStore = resultStore second
    ; resultSourceType = resultSourceType second
    ; resultTargetType = resultTargetType second
    ; sourceTypeResult =
        trans (sourceTypeResult second)
          (cong (applyTys (sourceChanges second))
            (sourceTypeResult first))
    ; targetTypeResult =
        trans (targetTypeResult second)
          (trans
            (cong (applyTys (targetTailChanges second))
              (targetTypeResult first))
            (sym (applyTys-++
              (targetTailChanges first)
              (targetTailChanges second) B)))
    ; transportType = source-silent-compose-type first refl second
    ; transportAllBody =
        source-silent-compose-all-body first refl second
    ; transportRightBody =
        source-silent-compose-right-body first refl second
    ; transportSourceNu =
        source-silent-compose-source-nu first refl second
    ; resultType = resultType second
    ; sourceCatchup = sourceCatchup second
    ; targetTail = ↠-trans (targetTail first) (targetTail second)
    ; sourceStoreResult =
        trans (sourceStoreResult second)
          (cong (applyStores (sourceChanges second))
            (sourceStoreResult first))
    ; targetStoreResult =
        trans (targetStoreResult second)
          (trans
            (cong (applyStores (targetTailChanges second))
              (targetStoreResult first))
            (sym (applyStores-++
              (targetTailChanges first)
              (targetTailChanges second) (rightStoreⁱ ρ))))
    ; relatedResults = relatedResults second
    }


source-silent-compose-transport-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  ∀ {L L′ C C′ p} →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⊑ C′ ∶ p →
  resultCtx second
    ∣ resultLeftCtx second
    ∣ resultRightCtx second
    ∣ resultStore second ∣ [] ⊢ᴺ
    applyTerms (sourceChanges second) L
    ⊑ applyTerms
        (targetTailChanges first ++ targetTailChanges second) L′
    ⦂ applyTys (sourceChanges second) C
      ⊑ applyTys
          (targetTailChanges first ++ targetTailChanges second) C′
    ∶ source-silent-compose-type first source-empty second p
source-silent-compose-transport-bodyᵀ
    first refl refl second first-transport second-transport
    {L′ = L′} {C = C} {C′ = C′} noL noL′ L⊑L′
    rewrite applyTerms-++
      (targetTailChanges first) (targetTailChanges second) L′
    | applyTys-++
      (targetTailChanges first) (targetTailChanges second) C′ =
  transportNo•Terms second-transport
    noL
    (applyTerms-preserves-No• (targetTailChanges first) noL′)
    (transportNo•Terms first-transport noL noL′ L⊑L′)


source-silent-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  WeakOneStepTransport
    (source-silent-resultᵀ first source-empty source-same second)
source-silent-preserves-transportᵀ
    first refl refl second
    first-transport second-transport =
  weak-step-transport
    (source-silent-compose-transport-bodyᵀ
      first refl refl second
      first-transport second-transport)


source-silent-compose-arrow-componentsᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  ∀ {C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  HE._≅_
    (subst
      (λ T → resultCtx second ∣ resultLeftCtx second
        ⊢ applyTys (sourceChanges second)
            (applyTys (sourceChanges first) C) ⇒
          applyTys (sourceChanges second)
            (applyTys (sourceChanges first) D)
          ⊑ T ⊣ resultRightCtx second)
    (cong₂ _⇒_
      (sym (applyTys-++
        (targetTailChanges first) (targetTailChanges second) C′))
      (sym (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D′)))
      (transportType second (transportType first pC) ↦
        transportType second (transportType first pD)))
    (source-silent-compose-type first source-empty second pC ↦
      source-silent-compose-type first source-empty second pD)
source-silent-compose-arrow-componentsᵀ
    first refl second {C′ = C′} {D′ = D′} pC pD =
  HE.≡-to-≅
    (transport-arrow-⊑ᵢ
      refl
      (sym (applyTys-++
        (targetTailChanges first) (targetTailChanges second) C′))
      refl
      (sym (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D′)))


source-silent-compose-all-componentsᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  ∀ {C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  HE._≅_
    (subst
      (λ T → resultCtx second ∣ resultLeftCtx second
        ⊢ `∀ (applyTysUnderTyBinders (sourceChanges second)
            (applyTysUnderTyBinders (sourceChanges first) C))
          ⊑ T ⊣ resultRightCtx second)
    (cong `∀
      (sym (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) C′)))
      (∀ⁱ (transportAllBody second (transportAllBody first q))))
    (∀ⁱ (source-silent-compose-all-body first source-empty second q))
source-silent-compose-all-componentsᵀ
    first refl second {C′ = C′} q =
  HE.≡-to-≅
    (transport-all-⊑ᵢ refl
      (sym (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) C′)))


source-silent-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  WeakOneStepTypeCoherence
    (source-silent-resultᵀ first source-empty source-same second)
source-silent-preserves-type-coherenceᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    first refl refl second first-coherence second-coherence =
  weak-step-type-coherence
    arrow-coherent all-coherent shape-coherent
    right-body-shape-coherent left-replacement-coherent
    right-replacement-coherent paired-replacement-coherent
    all-body-paired-replacement-coherent
    source-nu-body-left-replacement-coherent
    right-body-right-replacement-coherent
  where
  combined = source-silent-resultᵀ first refl refl second

  arrow-coherent :
    ∀ {C C′ D D′}
      (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
      (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
    transportArrowType combined pC pD ≡
      source-silent-compose-type first refl second pC ↦
      source-silent-compose-type first refl second pD
  arrow-coherent {C′ = C′} {D′ = D′} pC pD =
    HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ combined pC pD)
        (HE.trans
          (source-silent-compose-type-to-nested≅
            first refl second (pC ↦ pD))
          (HE.trans
            (weak-one-step-nested-arrow-coherent≅
              first second first-coherence second-coherence pC pD)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong₂ _⇒_ refl refl)
                  (cong₂ _⇒_
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (targetTailChanges second) C′))
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (targetTailChanges second) D′)))
                  (transportType second (transportType first pC) ↦
                    transportType second (transportType first pD))))
              (source-silent-compose-arrow-componentsᵀ
                first refl second pC pD)))))

  all-coherent :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    transportAllType combined q ≡
      ∀ⁱ (source-silent-compose-all-body first refl second q)
  all-coherent {C′ = C′} q =
    HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ combined q)
        (HE.trans
          (source-silent-compose-type-to-nested≅
            first refl second (∀ⁱ q))
          (HE.trans
            (weak-one-step-nested-all-coherent≅
              first second first-coherence second-coherence q)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong `∀ refl)
                  (cong `∀
                    (sym (applyTysUnderTyBinders-++
                      (targetTailChanges first)
                      (targetTailChanges second) C′)))
                  (∀ⁱ (transportAllBody second
                    (transportAllBody first q)))))
              (source-silent-compose-all-componentsᵀ
                first refl second q)))))

  shape-coherent :
    ∀ {C D}
      (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊
      (source-silent-compose-type first refl second p)
    ⌋ ≡ ⌊ p ⌋
  shape-coherent {D = D} p =
    trans
      (shape-subst-target target-eq nested)
      (trans
        (transportShapeCoherent second-coherence
          (transportType first p))
        (transportShapeCoherent first-coherence p))
    where
    nested = transportType second (transportType first p)
    target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D)

  composed-type-nested-shape :
    ∀ {C D}
      (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ source-silent-compose-type first refl second p ⌋ ≡
      ⌊
        transport-imprecision-endpoints refl
          (sym
            (applyTys-++
              (targetTailChanges first)
              (targetTailChanges second) D))
          (transportType second (transportType first p))
      ⌋
  composed-type-nested-shape {D = D} p =
    trans
      (shape-coherent p)
      (trans
        (sym (transportShapeCoherent first-coherence p))
        (trans
          (sym
            (transportShapeCoherent second-coherence
              (transportType first p)))
          (sym
            (shape-transport-imprecision-endpoints
              refl target-eq nested))))
    where
    nested = transportType second (transportType first p)
    target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D)

  right-body-shape-coherent :
    ∀ {C D}
      (p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ) →
    ⌊ source-silent-compose-right-body first refl second p ⌋
      ≡ ⌊ p ⌋
  right-body-shape-coherent {D = D} p =
    trans
      (shape-subst-target target-eq nested)
      (trans
        (transportRightBodyShapeCoherent second-coherence
          (transportRightBody first p))
        (transportRightBodyShapeCoherent first-coherence p))
    where
    nested = transportRightBody second (transportRightBody first p)
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) D)

  left-replacement-coherent :
    ∀ {C C′ D α X}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ C′ ⊣ Δᴿ} →
    p [ α ↦ X ]ᴸ q →
    source-silent-compose-type first refl second p
      [ applyTyVars (sourceChanges second) α
      ↦ applyTys (sourceChanges second) X ]ᴸ
    source-silent-compose-type first refl second q
  left-replacement-coherent
      {C′ = C′} {p = p} {q = q} replacement =
    replace-left-target-shape
      (composed-type-nested-shape q)
      (replace-left-source-shape
        (composed-type-nested-shape p)
        endpoints-replacement)
    where
    second-replacement =
      transportLeftReplacementCoherent second-coherence
        (transportLeftReplacementCoherent
          first-coherence replacement)

    target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) C′)

    endpoints-replacement =
      replace-left-transport-endpoints
        refl target-eq refl refl second-replacement

  right-replacement-coherent :
    ∀ {C C′ D′ β X′}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ D′ ⊣ Δᴿ} →
    p [ β ↦ X′ ]ᴿ q →
    source-silent-compose-type first refl second p
      [ applyTyVars
          (targetTailChanges first ++ targetTailChanges second) β
      ↦ applyTys
          (targetTailChanges first ++ targetTailChanges second) X′ ]ᴿ
    source-silent-compose-type first refl second q
  right-replacement-coherent
      {C′ = C′} {D′ = D′} {β = β} {X′ = X′}
      {p = p} {q = q} replacement
    rewrite applyTyVars-++
      (targetTailChanges first) (targetTailChanges second) β =
    replace-right-target-shape
      (composed-type-nested-shape q)
      (replace-right-source-shape
        (composed-type-nested-shape p)
        endpoints-replacement)
    where
    second-replacement =
      transportRightReplacementCoherent second-coherence
        (transportRightReplacementCoherent
          first-coherence replacement)

    input-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) C′)

    output-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D′)

    inserted-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) X′)

    endpoints-replacement =
      replace-right-transport-endpoints
        refl input-target-eq output-target-eq inserted-target-eq
        second-replacement

  paired-replacement-coherent :
    ∀ {C C′ D D′ α β X X′}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ} →
    p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    source-silent-compose-type first refl second p
      [ applyTyVars (sourceChanges second) α
      ↦ applyTys (sourceChanges second) X
      ⊑⟨ source-silent-compose-type first refl second pX ⟩
      applyTys
        (targetTailChanges first ++ targetTailChanges second) X′
      ↤ applyTyVars
          (targetTailChanges first ++ targetTailChanges second) β ]ᴾ
    source-silent-compose-type first refl second q
  paired-replacement-coherent
      {C′ = C′} {D′ = D′} {β = β} {X′ = X′}
      {pX = pX} {p = p} {q = q} replacement
    rewrite applyTyVars-++
      (targetTailChanges first) (targetTailChanges second) β =
    replace-paired-target-shape
      (composed-type-nested-shape q)
      (replace-paired-source-shape
        (composed-type-nested-shape p)
        (replace-paired-evidence-shape
          (composed-type-nested-shape pX)
          endpoints-replacement))
    where
    second-replacement =
      transportPairedReplacementCoherent second-coherence
        (transportPairedReplacementCoherent
          first-coherence replacement)

    input-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) C′)

    output-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) D′)

    inserted-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) X′)

    endpoints-replacement =
      replace-paired-transport-endpoints
        refl input-target-eq refl output-target-eq
        refl inserted-target-eq second-replacement

  ∀ˢ-injective-compose :
    ∀ {s t} →
    ∀ˢ s ≡ ∀ˢ t →
    s ≡ t
  ∀ˢ-injective-compose refl = refl

  first-all-type-raw-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllType first q ⌋ ≡
      ⌊ transportType first (∀ⁱ q) ⌋
  first-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType first (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges first) C
    source-transport =
      subst
        (λ S → resultCtx first ∣ resultLeftCtx first
          ⊢ S ⊑ applyTys (targetTailChanges first)
              (applyTy keep (`∀ C′))
          ⊣ resultRightCtx first)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges first))
          (applyTy-∀ keep C′))
        (applyTys-∀ (targetTailChanges first)
          (applyTyUnderTyBinder keep C′))

  first-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllBody first q ⌋ ≡ ⌊ q ⌋
  first-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent first-coherence q)))
        (trans
          (first-all-type-raw-shape q)
          (transportShapeCoherent first-coherence (∀ⁱ q))))

  second-all-type-raw-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ (resultCtx first) ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllType second q ⌋ ≡
      ⌊ transportType second (∀ⁱ q) ⌋
  second-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType second (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges second) C
    source-transport =
      subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTy keep (`∀ C′))
          ⊣ resultRightCtx second)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges second))
          (applyTy-∀ keep C′))
        (applyTys-∀ (targetTailChanges second)
          (applyTyUnderTyBinder keep C′))

  second-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ (resultCtx first) ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllBody second q ⌋ ≡ ⌊ q ⌋
  second-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent second-coherence q)))
        (trans
          (second-all-type-raw-shape q)
          (transportShapeCoherent second-coherence (∀ⁱ q))))

  composed-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ source-silent-compose-all-body first refl second q ⌋ ≡
      ⌊ q ⌋
  composed-all-body-shape {C′ = C′} q =
    trans
      (shape-subst-target target-eq nested)
      (trans
        (second-all-body-shape (transportAllBody first q))
        (first-all-body-shape q))
    where
    nested = transportAllBody second (transportAllBody first q)
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) C′)

  all-body-paired-replacement-coherent :
    ∀ {A A′ B B′ C C′}
      {A⇑⊑A′⇑ :
        ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    source-silent-compose-all-body first refl second q
      [ zero ↦
          applyTysUnderTyBinders (sourceChanges second) (⇑ᵗ A)
      ⊑⟨
        source-silent-compose-all-body
          first refl second A⇑⊑A′⇑
      ⟩
      applyTysUnderTyBinders
        (targetTailChanges first ++ targetTailChanges second)
        (⇑ᵗ A′)
      ↤ zero ]ᴾ
    ⊑-lift∀ᵢ
      (source-silent-compose-type first refl second pB)
  all-body-paired-replacement-coherent
      {A′ = A′} {B′ = B′} {C′ = C′}
      {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q}
      replacement =
    replace-paired-target-shape target-shape
      (replace-paired-source-shape source-shape
        (replace-paired-evidence-shape evidence-shape
          endpoints-replacement))
    where
    first-replacement =
      transportAllBodyPairedReplacementCoherent
        first-coherence replacement

    target-shift =
      applyTysUnderTyBinders-⇑ᵗ (targetTailChanges first) A′

    normalized-first-replacement =
      replace-paired-transport-endpoints
        refl refl refl refl refl target-shift first-replacement

    second-replacement =
      transportAllBodyPairedReplacementCoherent
        second-coherence normalized-first-replacement

    input-target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) C′)

    output-target-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (targetTailChanges first) (targetTailChanges second) B′))

    inserted-target-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (targetTailChanges second))
            target-shift))
        (sym
          (applyTysUnderTyBinders-++
            (targetTailChanges first)
            (targetTailChanges second) (⇑ᵗ A′)))

    endpoints-replacement =
      replace-paired-transport-endpoints
        refl input-target-eq refl output-target-eq
        refl inserted-target-eq second-replacement

    raw-input =
      transportAllBody second (transportAllBody first q)

    source-shape =
      trans
        (composed-all-body-shape q)
        (trans
          (sym (first-all-body-shape q))
          (trans
            (sym
              (second-all-body-shape
                (transportAllBody first q)))
            (sym
              (shape-transport-imprecision-endpoints
                refl input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-lift∀ᵢ nested-output

    target-shape =
      trans
        (shape-lift∀ᵢ
          (source-silent-compose-type first refl second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-lift∀ᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    refl output-target-eq raw-output))))))

    normalized-inserted =
      transport-imprecision-endpoints refl target-shift
        (transportAllBody first A⇑⊑A′⇑)

    raw-inserted = transportAllBody second normalized-inserted

    evidence-shape =
      trans
        (composed-all-body-shape A⇑⊑A′⇑)
        (trans
          (sym (first-all-body-shape A⇑⊑A′⇑))
          (trans
            (sym
              (shape-transport-imprecision-endpoints
                refl target-shift
                (transportAllBody first A⇑⊑A′⇑)))
            (trans
              (sym (second-all-body-shape normalized-inserted))
              (sym
                (shape-transport-imprecision-endpoints
                  refl inserted-target-eq raw-inserted)))))

  first-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody (transportSourceNu first safe occ q) ⌋
      ≡ ⌊ q ⌋
  first-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges first) C)
            (transportType first (ν safe occ q)))
          (transportShapeCoherent first-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu first safe occ q

  second-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx first))
        ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ D ⊣ resultRightCtx first) →
    ⌊ sourceNuBody (transportSourceNu second safe occ q) ⌋
      ≡ ⌊ q ⌋
  second-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges second) C)
            (transportType second (ν safe occ q)))
          (transportShapeCoherent second-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu second safe occ q

  composed-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody
        (source-silent-compose-source-nu
          first refl second safe occ q) ⌋
      ≡ ⌊ q ⌋
  composed-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges second) C)
            (source-silent-compose-type
              first refl second (ν safe occ q)))
          (shape-coherent (ν safe occ q))))
    where
    final-index =
      source-silent-compose-source-nu first refl second safe occ q

  source-nu-body-left-replacement-coherent :
    ∀ {A B B′ C}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true) →
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
    sourceNuBody
        (source-silent-compose-source-nu
          first refl second safe occ q)
      [ zero ↦
          applyTysUnderTyBinders (sourceChanges second) (⇑ᵗ A) ]ᴸ
    ⊑-source-liftνᵢ
      (source-silent-compose-type first refl second pB)
  source-nu-body-left-replacement-coherent
      {B′ = B′} {pB = pB} {q = q}
      safe occ replacement =
    replace-left-target-shape target-shape
      (replace-left-source-shape source-shape endpoints-replacement)
    where
    first-index = transportSourceNu first safe occ q

    first-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        first-coherence safe occ replacement

    second-index =
      transportSourceNu second
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        (sourceNuBody first-index)

    second-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        second-coherence
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        first-replacement

    input-target-eq = sym
      (applyTys-++
        (targetTailChanges first) (targetTailChanges second) B′)

    endpoints-replacement =
      replace-left-transport-endpoints
        refl input-target-eq refl refl second-replacement

    raw-input = sourceNuBody second-index

    source-shape =
      trans
        (composed-source-nu-body-shape safe occ q)
        (trans
          (sym (first-source-nu-body-shape safe occ q))
          (trans
            (sym
              (second-source-nu-body-shape
                (sourceNuSafe first-index)
                (sourceNuOccurs first-index)
                (sourceNuBody first-index)))
            (sym
              (shape-transport-imprecision-endpoints
                refl input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-source-liftνᵢ nested-output

    target-shape =
      trans
        (shape-source-liftνᵢ
          (source-silent-compose-type first refl second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-source-liftνᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    refl input-target-eq raw-output))))))

  right-body-right-replacement-coherent :
    ∀ {A B B′ C′}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
    pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
    source-silent-compose-right-body first refl second pC
      [ zero ↦
          applyTysUnderTyBinders
            (targetTailChanges first ++ targetTailChanges second)
            (⇑ᵗ A) ]ᴿ
    ⊑-target-lift-rightᵢ
      (source-silent-compose-type first refl second pB)
  right-body-right-replacement-coherent
      {A = A} {B′ = B′} {C′ = C′}
      {pB = pB} {pC = pC} replacement =
    replace-right-target-shape target-shape
      (replace-right-source-shape source-shape endpoints-replacement)
    where
    first-replacement =
      transportRightBodyRightReplacementCoherent
        first-coherence replacement

    target-shift =
      applyTysUnderTyBinders-⇑ᵗ (targetTailChanges first) A

    normalized-first-replacement =
      replace-right-transport-endpoints
        refl refl refl target-shift first-replacement

    second-replacement =
      transportRightBodyRightReplacementCoherent
        second-coherence normalized-first-replacement

    input-target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first) (targetTailChanges second) C′)

    output-target-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (targetTailChanges first) (targetTailChanges second) B′))

    inserted-target-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (targetTailChanges second))
            target-shift))
        (sym
          (applyTysUnderTyBinders-++
            (targetTailChanges first)
            (targetTailChanges second) (⇑ᵗ A)))

    endpoints-replacement =
      replace-right-transport-endpoints
        refl input-target-eq output-target-eq inserted-target-eq
        second-replacement

    raw-input =
      transportRightBody second (transportRightBody first pC)

    source-shape =
      trans
        (right-body-shape-coherent pC)
        (trans
          (sym
            (transportRightBodyShapeCoherent first-coherence pC))
          (trans
            (sym
              (transportRightBodyShapeCoherent second-coherence
                (transportRightBody first pC)))
            (sym
              (shape-transport-imprecision-endpoints
                refl input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-target-lift-rightᵢ nested-output

    target-shape =
      trans
        (shape-target-lift-rightᵢ
          (source-silent-compose-type first refl second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-target-lift-rightᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    refl output-target-eq raw-output))))))


source-silent-preserves-store-lineageᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  WeakOneStepStoreLineage first →
  WeakOneStepStoreLineage second →
  WeakOneStepStoreLineage
    (source-silent-resultᵀ first source-empty source-same second)
source-silent-preserves-store-lineageᵀ
    first refl refl second
    (weak-step-store-lineage store₁ embedding₁ prefix₁)
    (weak-step-store-lineage store₂ embedding₂ prefix₂)
    with rel-store-embedding-prefix-invⁱ prefix₁ embedding₂
source-silent-preserves-store-lineageᵀ
    first refl refl second
    (weak-step-store-lineage store₁ embedding₁ prefix₁)
    (weak-step-store-lineage store₂ embedding₂ prefix₂)
    | store₁₂ , embedding₁₂ , prefix₁₂ =
  weak-step-store-lineage store₁₂
    (rel-store-embedding-congⁱ
      (λ α → refl)
      (λ β → sym
        (applyTyVars-++
          (targetTailChanges first)
          (targetTailChanges second) β))
      (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
    (store-imp-prefix-transⁱ prefix₁₂ prefix₂)


source-silent-preserves-changes-exactᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep)
    {χs} →
  sourceChanges second ≡ χs →
  sourceChanges
    (source-silent-resultᵀ first source-empty source-same second) ≡ χs
source-silent-preserves-changes-exactᵀ
    first refl refl second exact = exact


source-silent-preserves-result-exactᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep)
    {L} →
  sourceResult second ≡ L →
  sourceResult
    (source-silent-resultᵀ first source-empty source-same second) ≡ L
source-silent-preserves-result-exactᵀ
    first refl refl second exact = exact


source-silent-preserves-world-coherentᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  WorldCoherent (resultStore second) →
  WorldCoherent
    (resultStore
      (source-silent-resultᵀ first source-empty source-same second))
source-silent-preserves-world-coherentᵀ
    first refl refl second coherent = coherent


source-silent-preserves-source-name-exclusiveᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  SourceNameExclusive (resultCtx second) →
  SourceNameExclusive
    (resultCtx
      (source-silent-resultᵀ first source-empty source-same second))
source-silent-preserves-source-name-exclusiveᵀ
    first refl refl second exclusive = exclusive


source-silent-preserves-assumption-membership-uniqueᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep)
    (source-empty : sourceChanges first ≡ [])
    (source-same : sourceResult first ≡ M)
    (second : WeakOneStepResult
      (resultStore first)
      (sourceResult first)
      (targetResult first)
      (resultSourceType first)
      (resultTargetType first)
      keep) →
  AssumptionMembershipUnique (resultCtx second) →
  AssumptionMembershipUnique
    (resultCtx
      (source-silent-resultᵀ first source-empty source-same second))
source-silent-preserves-assumption-membership-uniqueᵀ
    first refl refl second unique = unique


source-silent-composition-proofᵀ : SourceSilentComposition
source-silent-composition-proofᵀ =
  record
    { sourceSilentResult = source-silent-resultᵀ
    ; sourceSilentTransport = source-silent-preserves-transportᵀ
    ; sourceSilentTypeCoherence =
        source-silent-preserves-type-coherenceᵀ
    ; sourceSilentStoreLineage =
        source-silent-preserves-store-lineageᵀ
    ; sourceSilentChangesExact =
        source-silent-preserves-changes-exactᵀ
    ; sourceSilentResultExact =
        source-silent-preserves-result-exactᵀ
    ; sourceSilentWorldCoherent =
        source-silent-preserves-world-coherentᵀ
    ; sourceSilentSourceNameExclusive =
        source-silent-preserves-source-name-exclusiveᵀ
    ; sourceSilentAssumptionMembershipUnique =
        source-silent-preserves-assumption-membership-uniqueᵀ
    }
