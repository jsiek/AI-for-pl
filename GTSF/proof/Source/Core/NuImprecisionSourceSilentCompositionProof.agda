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
open import ImprecisionWf using (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_; ν)
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
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (occurs; _⇒_; `∀)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( ≡-to-≅
  ; subst-to-≅
  ; subst²-to-≅
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transportSourceNuType-to-raw≅
  ; transportType-source-subst-to-raw≅
  ; weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  ; weak-one-step-nested-source-nu≅
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
  ; applyTyCtxs-++
  ; applyTys-++
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
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
  ≡-to-≅
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
  ≡-to-≅
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
  weak-step-type-coherence arrow-coherent all-coherent
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
