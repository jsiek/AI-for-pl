module proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepProof where

-- File Charter:
--   * Proves the source allocation root by structural recursion on the
--     quotiented term-precision derivation.
--   * Delegates the exact target-bullet crossing and right-value catch-up to
--     higher-order capabilities while preserving the existing flat result.
--   * Contains no postulate, hole, permissive option, dispatcher, or new
--     result carrier.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Coercions using (instᵈ; src)
open import Conversion using
  ( conceal-conversion-typing
  ; conversion↑⇒coercion
  ; conversion↓⇒coercion
  ; reveal-conversion-typing
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ) renaming (ν to νⁱ)
open import NarrowWiden using (widen-weaken)
open import NuReduction using
  ( bind
  ; applyTy
  ; applyTys
  ; applyCoercionUnderTyBinder
  ; keep
  ; StoreChange
  ; _—→[_]_
  ; ν-step
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreIncl-cons; StoreWf)
open import NuTermImprecision using
  ( LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; lift-right-ctx-[]
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  ; rightStoreⁱ-lift-left
  ; store-left
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; no•-ν
  ; ok-no
  ; ok-⟨⟩
  ; ok-ν
  ; ν
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; allocation-prefixᵀ
  ; conv↑⊑ᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ⊑αᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢ν↑
  ; ⊢ν⊑
  )
open import Types using
  (Ty; TyCtx; WfTy; ★; _⇒_; `∀; extᵗ; renameᵗ; ⇑ᵗ)
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  )
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  ( left-ν↑-allocation
  ; left-νcast-allocation
  ; weak-one-step-matched-ν↑-type-coherenceᵀ
  ; weak-one-step-matched-ν↑-transportᵀ
  ; weak-one-step-matched-ν↑ᵀ
  ; weak-one-step-matched-νcast-type-coherenceᵀ
  ; weak-one-step-matched-νcast-transportᵀ
  ; weak-one-step-matched-νcastᵀ
  ; weak-result-transport-paired-widening-compatible-under-binderᵀ
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  ( source-name-exclusive-matched-head
  ; source-name-exclusive-source-only-head
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.Left.Core.NuImprecisionLeftLiftPrefixBodyProof using
  (left-lift-prefix-body-proofᵀ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( lift-left-store-embeddingⁱ
  ; lift-store-embeddingⁱ
  ; rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( equality-proof-unique
  ; nu-term-imprecision-transport-typesᵀ
  ; renameᵗ-ext-id
  ; subst²-to-≅
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; weak-indexed-all-resultᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-compose-all-body
  ; weak-one-step-compose-all-componentsᵀ
  ; weak-one-step-compose-arrow-componentsᵀ
  ; weak-one-step-compose-preserves-transportᵀ
  ; weak-one-step-compose-type
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-composeᵀ
  ; weak-one-step-matched-ν-frame-preserves-transportᵀ
  ; weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-ν-frameᵀ
  ; weak-one-step-matched-νcast-frame-preserves-transportᵀ
  ; weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-νcast-frameᵀ
  ; weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  ; weak-result-source-reveal
  ; weak-result-source-widen-inst
  ; weak-result-target-reveal
  ; weak-result-target-widen-inst
  ; ⊑-source-under-rightᵢ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepAllResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; canonicalAllResults
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceResult
  ; sourceTypeResult
  ; targetTailChanges
  ; targetResult
  ; targetTypeResult
  ; transportType
  ; transportAllBody
  ; transportAllType
  ; transportArrowType
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; weak-step-store-lineage
  )
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-left-store-result; lift-store-result)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation; world-coherent-matched-allocation)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  )
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( RightValueCatchupIndexedResult
  ; right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepDef using
  (WorldCoherentSourceAllocationStepᵀ)
open import
  proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationPairedIndexStepsDef
  using
  ( WorldCoherentSourceAllocationPairedIndexSteps
  ; sourceAllocationNuCastPairedIndexStep
  ; sourceAllocationNuPairedIndexStep
  )
open import
  proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationTargetBulletStepDef
  using (WorldCoherentSourceAllocationTargetBulletStepᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (sourceStepTargetNuCastFrame; sourceStepTargetNuFrame)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesLemma
  using (world-coherent-source-one-step-target-nu-framesᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.ReductionProperties using
  ( applyTyUnderTyBinder
  ; applyTyVars-++
  ; applyTys-★
  ; applyTys-++
  ; applyTysUnderTyBinders-++
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-ext; TyRenameWf-suc; renameᵗ-id)


ν-runtime : ∀ {A N s} → RuntimeOK (ν A N s) → RuntimeOK N
ν-runtime (ok-no (no•-ν no-N)) = ok-no no-N
ν-runtime (ok-ν ok-N) = ok-N


cast-runtime : ∀ {M c} → RuntimeOK (M ⟨ c ⟩) → RuntimeOK M
cast-runtime (ok-no (no•-⟨⟩ no-M)) = ok-no no-M
cast-runtime (ok-⟨⟩ ok-M) = ok-M


ν-body-typing-at :
  ∀ {Δ Σ Γ A N s B C} →
  src s ≡ C →
  Δ ∣ Σ ∣ Γ ⊢ ν A N s ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ N ⦂ `∀ C
ν-body-typing-at src≡C (⊢ν↑ hA N⊢ s⊢) =
  subst (λ X → _ ∣ _ ∣ _ ⊢ _ ⦂ `∀ X)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↑⇒coercion s⊢)))) src≡C) N⊢
ν-body-typing-at src≡C (⊢ν⊑ mode seal★ N⊢ s⊢) =
  subst (λ X → _ ∣ _ ∣ _ ⊢ _ ⦂ `∀ X)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ s⊢)))) src≡C)
    N⊢


cast-body-typing-at :
  ∀ {Δ Σ Γ M c A B} →
  src c ≡ A →
  Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
cast-body-typing-at src≡A (⊢⟨⟩↑ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↑⇒coercion c⊢)))) src≡A) M⊢
cast-body-typing-at src≡A (⊢⟨⟩↓ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ
      (conversion↓⇒coercion c⊢)))) src≡A) M⊢
cast-body-typing-at src≡A (⊢⟨⟩⊒ mode seal★ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A)
    M⊢
cast-body-typing-at src≡A (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
  subst (_ ∣ _ ∣ _ ⊢ _ ⦂_)
    (trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ c⊢)))) src≡A)
    M⊢


private
  source-lift-under-∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A B} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
    ((zero ˣ⊑ˣ zero) ∷
      ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc (suc Δᴸ)
      ⊢ renameᵗ (extᵗ suc) A ⊑ B ⊣ suc Δᴿ
  source-lift-under-∀ᵢ {B = B} p =
    subst (λ T → _ ∣ _ ⊢ renameᵗ (extᵗ suc) _ ⊑ T ⊣ _)
      (renameᵗ-ext-id B)
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-source-νᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p)

  source-lift-arrowᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′}
      (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
      (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    ⊑-source-liftνᵢ (pA ↦ pB) ≡
      ⊑-source-liftνᵢ pA ↦ ⊑-source-liftνᵢ pB
  source-lift-arrowᵢ {A′ = A′} {B′ = B′} pA pB
      rewrite equality-proof-unique
          (renameᵗ-id (A′ ⇒ B′))
          (cong₂ _⇒_ (renameᵗ-id A′) (renameᵗ-id B′)) =
    transport-arrow-⊑ᵢ
      refl (renameᵗ-id A′) refl (renameᵗ-id B′)

  source-lift-allᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
    ⊑-source-liftνᵢ (∀ⁱ p) ≡ ∀ⁱ (source-lift-under-∀ᵢ p)
  source-lift-allᵢ {A = A} {B = B} p
      rewrite equality-proof-unique
          (renameᵗ-id (`∀ B))
          (cong `∀ (renameᵗ-ext-id B)) =
    transport-all-⊑ᵢ refl (renameᵗ-ext-id B)


  weak-one-step-compose-store-lineageᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B χ)
      {χ′ : StoreChange} {N′} →
    (target→ : targetResult first —→[ χ′ ] N′) →
    (second : WeakOneStepResult
      (resultStore first) (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
    WeakOneStepStoreLineage first →
    WeakOneStepStoreLineage second →
    WeakOneStepStoreLineage
      (weak-one-step-composeᵀ first target→ second)
  weak-one-step-compose-store-lineageᵀ
      first target→ second
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      with rel-store-embedding-prefix-invⁱ prefix₁ embedding₂
  weak-one-step-compose-store-lineageᵀ
      { χ = χ } first {χ′ = χ′} target→ second
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      | store₁₂ , embedding₁₂ , prefix₁₂ =
    weak-step-store-lineage store₁₂
      (rel-store-embedding-congⁱ
        (λ α → sym
          (applyTyVars-++
            (sourceChanges first) (sourceChanges second) α))
        (λ β → sym
          (applyTyVars-++
            (χ ∷ targetTailChanges first)
            (χ′ ∷ targetTailChanges second) β))
        (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
      (store-imp-prefix-transⁱ prefix₁₂ prefix₂)


  weak-one-step-reindex-preserves-store-lineageᵀ :
    ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ M N′ A B χ)
      {C D}
      {r : resultCtx result ∣ resultLeftCtx result
        ⊢ C ⊑ D ⊣ resultRightCtx result}
      (source-eq : C ≡ applyTys (sourceChanges result) A)
      (target-eq : D ≡
        applyTys (targetTailChanges result) (applyTy χ B))
      (related : resultCtx result
        ∣ resultLeftCtx result
        ∣ resultRightCtx result
        ∣ resultStore result ∣ []
        ⊢ᴺ sourceResult result ⊑ targetResult result
        ⦂ C ⊑ D ∶ r) →
    WeakOneStepStoreLineage result →
    WeakOneStepStoreLineage
      (weak-one-step-reindexᵀ
        result source-eq target-eq related)
  weak-one-step-reindex-preserves-store-lineageᵀ
      result source-eq target-eq related
      (weak-step-store-lineage store embedding prefix) =
    weak-step-store-lineage store embedding prefix


  weak-one-step-compose-preserves-type-coherence-localᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B χ)
      {χ′ N′}
      (target→ : targetResult first —→[ χ′ ] N′)
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (resultSourceType first) (resultTargetType first) χ′) →
    WeakOneStepTypeCoherence first →
    WeakOneStepTypeCoherence second →
    WeakOneStepTypeCoherence
      (weak-one-step-composeᵀ first target→ second)
  weak-one-step-compose-preserves-type-coherence-localᵀ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {χ = χ}
      first {χ′ = χ′} target→ second
      first-coherence second-coherence =
    weak-step-type-coherence arrow-coherent all-coherent
    where
    combined = weak-one-step-composeᵀ first target→ second

    arrow-coherent :
      ∀ {C C′ D D′}
        (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
        (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
      transportArrowType combined pC pD ≡
        weak-one-step-compose-type first second pC ↦
        weak-one-step-compose-type first second pD
    arrow-coherent {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
      HE.≅-to-≡
        (HE.trans
          (transportArrowType-to-raw≅ combined pC pD)
          (HE.trans
            (weak-one-step-compose-type-to-nested≅
              first second (pC ↦ pD))
            (HE.trans
              (weak-one-step-nested-arrow-coherent≅
                first second first-coherence second-coherence pC pD)
              (HE.trans
                (HE.sym
                  (subst²-to-≅
                    {P = λ S T →
                      resultCtx second ∣ resultLeftCtx second
                        ⊢ S ⊑ T ⊣ resultRightCtx second}
                    (cong₂ _⇒_
                      (sym (applyTys-++
                        (sourceChanges first)
                        (sourceChanges second) C))
                      (sym (applyTys-++
                        (sourceChanges first)
                        (sourceChanges second) D)))
                    (cong₂ _⇒_
                      (sym (applyTys-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTy χ C′)))
                      (sym (applyTys-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTy χ D′))))
                    (transportType second (transportType first pC) ↦
                      transportType second (transportType first pD))))
                (HE.≡-to-≅
                  (weak-one-step-compose-arrow-componentsᵀ
                    first second pC pD))))))

    all-coherent :
      ∀ {C C′}
        (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      transportAllType combined q ≡
        ∀ⁱ (weak-one-step-compose-all-body first second q)
    all-coherent {C = C} {C′ = C′} q =
      HE.≅-to-≡
        (HE.trans
          (transportAllType-to-raw≅ combined q)
          (HE.trans
            (weak-one-step-compose-type-to-nested≅
              first second (∀ⁱ q))
            (HE.trans
              (weak-one-step-nested-all-coherent≅
                first second first-coherence second-coherence q)
              (HE.trans
                (HE.sym
                  (subst²-to-≅
                    {P = λ S T →
                      resultCtx second ∣ resultLeftCtx second
                        ⊢ S ⊑ T ⊣ resultRightCtx second}
                    (cong `∀
                      (sym (applyTysUnderTyBinders-++
                        (sourceChanges first)
                        (sourceChanges second) C)))
                    (cong `∀
                      (sym (applyTysUnderTyBinders-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTyUnderTyBinder χ C′))))
                    (∀ⁱ (transportAllBody second
                      (transportAllBody first q)))))
                (HE.≡-to-≅
                  (weak-one-step-compose-all-componentsᵀ
                    first second q))))))


  compose-exact-source-stepᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ L : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {χ χ′ : StoreChange} →
    (first-indexed : WeakOneStepIndexedResult
      {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p) →
    let first-raw = weakIndexedResult first-indexed
        first = weak-one-step-reindexᵀ first-raw refl refl
          (canonicalIndexedResults first-indexed)
    in
    (target→ : targetResult first —→[ χ′ ] N′) →
    (second-indexed : WeakOneStepIndexedResult
      {M = sourceResult first} {N′ = N′} {χ = χ′}
      {ρ = resultStore first} (resultType first)) →
    WeakOneStepTransport first-raw →
    WeakOneStepTypeCoherence first-raw →
    WeakOneStepStoreLineage first-raw →
    WeakOneStepTransport (weakIndexedResult second-indexed) →
    WeakOneStepTypeCoherence (weakIndexedResult second-indexed) →
    WeakOneStepStoreLineage (weakIndexedResult second-indexed) →
    sourceChanges
      (weak-one-step-composeᵀ first target→
        (weakIndexedResult second-indexed)) ≡ χ ∷ [] →
    sourceResult (weakIndexedResult second-indexed) ≡ L →
    WorldCoherent (resultStore (weakIndexedResult second-indexed)) →
    SourceNameExclusive
      (resultCtx (weakIndexedResult second-indexed)) →
    AssumptionMembershipUnique
      (resultCtx (weakIndexedResult second-indexed)) →
    WorldCoherentSourceOneStepIndexedResult
      {M = M} {M′ = M′} {L = L}
      {χ = χ} {ρ = ρ} p
  compose-exact-source-stepᵀ
      {p = p} first-indexed target→ second-indexed
      first-transport first-coherence first-lineage
      second-transport second-coherence second-lineage
      changes-exact result-exact final-world final-exclusive final-unique =
    world-coherent-source-one-step-indexed
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      combined-lineage
      changes-exact result-exact final-world final-exclusive final-unique
    where
    first-raw = weakIndexedResult first-indexed
    first = weak-one-step-reindexᵀ first-raw refl refl
      (canonicalIndexedResults first-indexed)
    second-raw = weakIndexedResult second-indexed
    second = weak-one-step-reindexᵀ second-raw refl refl
      (canonicalIndexedResults second-indexed)
    combined = weak-one-step-composeᵀ first target→ second

    type-eq = HE.≅-to-≡
      (HE.trans
        (subst²-to-≅
          {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
            ⊢ S ⊑ T ⊣ resultRightCtx combined}
          (sourceTypeResult combined)
          (targetTypeResult combined)
          (resultType combined))
        (HE.sym
          (weak-one-step-compose-type-to-nested≅ first second p)))

    first-transport′ =
      weak-one-step-reindex-preserves-transportᵀ
        first-raw refl refl (canonicalIndexedResults first-indexed)
        first-transport

    first-coherence′ =
      weak-one-step-reindex-preserves-type-coherenceᵀ
        first-raw refl refl (canonicalIndexedResults first-indexed)
        first-coherence

    first-lineage′ =
      weak-one-step-reindex-preserves-store-lineageᵀ
        first-raw refl refl (canonicalIndexedResults first-indexed)
        first-lineage

    second-transport′ =
      weak-one-step-reindex-preserves-transportᵀ
        second-raw refl refl (canonicalIndexedResults second-indexed)
        second-transport

    second-coherence′ =
      weak-one-step-reindex-preserves-type-coherenceᵀ
        second-raw refl refl (canonicalIndexedResults second-indexed)
        second-coherence

    second-lineage′ =
      weak-one-step-reindex-preserves-store-lineageᵀ
        second-raw refl refl (canonicalIndexedResults second-indexed)
        second-lineage

    raw-transport =
      weak-one-step-compose-preserves-transportᵀ
        first target→ second first-transport′ second-transport′
    combined-transport = raw-transport

    raw-coherence =
      weak-one-step-compose-preserves-type-coherence-localᵀ
        first target→ second first-coherence′ second-coherence′
    combined-coherence = raw-coherence

    combined-lineage =
      weak-one-step-compose-store-lineageᵀ
        first target→ second first-lineage′ second-lineage′


world-coherent-source-allocation-step-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceAllocationPairedIndexSteps →
  WorldCoherentSourceAllocationTargetBulletStepᵀ →
  WorldCoherentSourceAllocationStepᵀ
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (allocation-prefixᵀ prefix₀ inner inner-source⊢ inner-target⊢)
    vV noV =
  world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet
    (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfL wfR ok-source ok-target source⊢ target⊢
    inner vV noV
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet
    prefix coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑ᵀ {q = ∀ⁱ q}
      hA h⇑A s↑ liftρ lift-left-ctx-[] inner)
    vV noV =
  sourceAllocationNuPairedIndexStep paired-steps
    prefix coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    hA h⇑A s↑ liftρ lift-left-ctx-[] inner vV noV
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑ᵀ {q = νⁱ safe occ q}
      hA h⇑A s↑ liftρ lift-left-ctx-[] inner)
    vV noV
    with lift-left-store-result _
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑ᵀ {q = νⁱ safe occ q}
      hA h⇑A s↑ liftρ lift-left-ctx-[] inner)
    vV noV
    | ρ↑ , liftρ⁺
    with left-ν↑-allocation {{safe = safe}}
      vV noV h⇑A
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        s↑)
      _ liftρ⁺
      (allocation-prefixᵀ prefix inner
        (ν-body-typing-at
          (proj₁ (coercion-src-tgtᵐ
            (conversion↑⇒coercion
              (reveal-conversion-typing s↑))))
          source⊢)
        target⊢)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑ᵀ {q = νⁱ safe occ q}
      hA h⇑A s↑ liftρ lift-left-ctx-[] inner)
    vV noV
    | ρ↑ , liftρ⁺ | source-step , target-refl , related =
  world-coherent-source-one-step-indexed
    (weak-indexed-result result related
      (weak-step-transport
        (left-lift-prefix-body-proofᵀ
          liftρ⁺ (prefix-∷ⁱ prefix-reflⁱ)))
      (weak-step-type-coherence source-lift-arrowᵢ source-lift-allᵢ))
    (weak-step-store-lineage ρ↑
      (lift-left-store-embeddingⁱ liftρ⁺)
      (prefix-∷ⁱ prefix-reflⁱ))
    refl refl
    (world-coherent-left-allocation liftρ⁺ coherent)
    (source-name-exclusive-source-only-head exclusive)
    (assumption-membership-unique-source unique)
  where
  result : WeakOneStepResult _ _ _ _ _ keep
  result =
    record
      { sourceChanges = bind _ ∷ []
      ; targetTailChanges = []
      ; sourceResult = _
      ; targetResult = _
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
      ; resultLeftCtx = suc _
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = store-left zero (⇑ᵗ _) h⇑A ∷ ρ↑
      ; resultSourceType = ⇑ᵗ _
      ; resultTargetType = _
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-source-liftνᵢ
      ; transportAllBody = source-lift-under-∀ᵢ
      ; transportRightBody = ⊑-source-under-rightᵢ
      ; resultType = ⊑-source-liftνᵢ _
      ; sourceCatchup = ↠-step source-step ↠-refl
      ; targetTail = target-refl
      ; sourceStoreResult =
          cong ((zero , ⇑ᵗ _) ∷_) (leftStoreⁱ-lift-left liftρ⁺)
      ; targetStoreResult = rightStoreⁱ-lift-left liftρ⁺
      ; relatedResults = related
      }
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet
    prefix coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑ᵀ {q = ∀ⁱ q}
      mode seal★ s⊑ liftρ lift-left-ctx-[] inner)
    vV noV =
  sourceAllocationNuCastPairedIndexStep paired-steps
    prefix coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢
    mode seal★ s⊑ liftρ lift-left-ctx-[] inner vV noV
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑νcastᵀ {p = pB}
      mode seal★ mode′ seal★′ s⊑ s′⊑ compat
      liftρ lift-ctx inner)
    vV noV
    with right-catchup prefix coherent exclusive unique wfR
      (ν-runtime ok-target) vV noV inner
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑νcastᵀ {p = pB}
      mode seal★ mode′ seal★′ s⊑ s′⊑ compat
      liftρ lift-ctx inner)
    vV noV
    | world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          caught-vV caught-noV caught-vV′ caught-noV′)
        (weak-step-store-lineage
          lineage-store lineage-embedding lineage-prefix)
        source-bullet-transport final-coherent final-exclusive final-unique
          final-wfR
    =
  compose-exact-source-stepᵀ
    first-indexed target-step second-indexed
    first-transport first-coherence first-lineage
    second-transport second-coherence second-lineage
    refl refl final-world final-exclusive⁺ final-unique⁺
  where
  all = weak-indexed-all-resultᵀ indexed
  inner-result = weakIndexedResult indexed

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken source-store-incl seal★
  s⊑⁺ = widen-weaken ≤-refl source-store-incl s⊑
  seal★′⁺ = seal★-weaken target-store-incl seal★′
  s′⊑⁺ = widen-weaken ≤-refl target-store-incl s′⊑

  framed = weak-one-step-matched-νcast-frameᵀ
    mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all

  target-step = ν-step caught-vV′ caught-noV′

  liftρ⁺ = proj₂ (lift-store-result (resultStore inner-result))

  source-widen =
    weak-result-source-widen-inst inner-result mode seal★⁺ s⊑⁺
  source-mode⁺ = proj₁ (proj₂ source-widen)
  source-seal⁺ = proj₁ (proj₂ (proj₂ source-widen))
  source-s⊑⁺ = proj₂ (proj₂ (proj₂ source-widen))

  target-widen = weak-result-target-widen-inst
    keep inner-result mode′ seal★′⁺ s′⊑⁺
  target-mode⁺ = proj₁ (proj₂ target-widen)
  target-seal⁺ = proj₁ (proj₂ (proj₂ target-widen))
  target-s⊑⁺ = proj₂ (proj₂ (proj₂ target-widen))

  compat⁺ =
    weak-result-transport-paired-widening-compatible-under-binderᵀ
      inner-result compat

  final-inner = canonicalAllResults all

  second = weak-one-step-matched-νcastᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source-mode⁺ source-seal⁺ target-mode⁺ target-seal⁺
    source-s⊑⁺ target-s⊑⁺ compat⁺
    (transportType inner-result pB) liftρ⁺ final-inner

  first-transport =
    weak-one-step-matched-νcast-frame-preserves-transportᵀ
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
      mode seal★⁺ s⊑⁺ mode′ seal★′⁺ s′⊑⁺ compat pB all
      (weakIndexedTypeCoherence indexed)

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  second-transport = weak-one-step-matched-νcast-transportᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source-mode⁺ source-seal⁺ target-mode⁺ target-seal⁺
    source-s⊑⁺ target-s⊑⁺ compat⁺
    (transportType inner-result pB) liftρ⁺ final-inner

  second-coherence = weak-one-step-matched-νcast-type-coherenceᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source-mode⁺ source-seal⁺ target-mode⁺ target-seal⁺
    source-s⊑⁺ target-s⊑⁺ compat⁺
    (transportType inner-result pB) liftρ⁺ final-inner

  first-indexed =
    weak-indexed-result framed (relatedResults framed)
      first-transport first-coherence

  second-indexed = weak-one-step-index-resultᵀ second refl
    second-transport second-coherence

  second-lineage = weak-step-store-lineage _
    (lift-store-embeddingⁱ liftρ⁺) (prefix-∷ⁱ prefix-reflⁱ)

  final-world = world-coherent-matched-allocation liftρ⁺ final-coherent

  final-exclusive⁺ =
    source-name-exclusive-matched-head final-exclusive

  final-unique⁺ =
    assumption-membership-unique-matched final-unique
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑νᵀ {p = pB}
      hA hA′ s↑ s′↑ pA A⇑⊑A′⇑ liftρ lift-ctx inner)
    vV noV
    with right-catchup prefix coherent exclusive unique wfR
      (ν-runtime ok-target) vV noV inner
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (ν⊑νᵀ {p = pB}
      hA hA′ s↑ s′↑ pA A⇑⊑A′⇑ liftρ lift-ctx inner)
    vV noV
    | world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          caught-vV caught-noV caught-vV′ caught-noV′)
        (weak-step-store-lineage
          lineage-store lineage-embedding lineage-prefix)
        source-bullet-transport final-coherent final-exclusive final-unique
          final-wfR
    =
  compose-exact-source-stepᵀ
    first-indexed target-step second-indexed
    first-transport first-coherence first-lineage
    second-transport second-coherence second-lineage
    refl refl final-world final-exclusive⁺ final-unique⁺
  where
  all = weak-indexed-all-resultᵀ indexed

  source↑ = weaken-reveal-conversion
    (StoreIncl-cons
      (renameStoreᵗ-incl suc
        (leftStoreⁱ-prefix-inclusion prefix)))
    s↑

  target↑ = weaken-reveal-conversion
    (StoreIncl-cons
      (renameStoreᵗ-incl suc
        (rightStoreⁱ-prefix-inclusion prefix)))
    s′↑

  framed = weak-one-step-matched-ν-frameᵀ
    source↑ target↑ pA pB all

  target-step = ν-step caught-vV′ caught-noV′

  inner-result = weakIndexedResult indexed

  liftρ⁺ = proj₂ (lift-store-result (resultStore inner-result))

  source↑⁺ = proj₂ (weak-result-source-reveal inner-result source↑)

  target↑⁺ =
    proj₂ (weak-result-target-reveal keep inner-result target↑)

  final-inner = canonicalAllResults all

  A⇑⊑A′⇑⁺ = ⊑-lift∀ᵢ (transportType inner-result pA)

  second = weak-one-step-matched-ν↑ᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source↑⁺ target↑⁺ (transportType inner-result pB)
    A⇑⊑A′⇑⁺ liftρ⁺ final-inner

  first-transport =
    weak-one-step-matched-ν-frame-preserves-transportᵀ
      source↑ target↑ pA pB all (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      source↑ target↑ pA pB all (weakIndexedTypeCoherence indexed)

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  second-transport = weak-one-step-matched-ν↑-transportᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source↑⁺ target↑⁺ (transportType inner-result pB)
    A⇑⊑A′⇑⁺ liftρ⁺ final-inner

  second-coherence = weak-one-step-matched-ν↑-type-coherenceᵀ
    caught-vV caught-noV caught-vV′ caught-noV′
    source↑⁺ target↑⁺ (transportType inner-result pB)
    A⇑⊑A′⇑⁺ liftρ⁺ final-inner

  first-indexed =
    weak-indexed-result framed (relatedResults framed)
      first-transport first-coherence

  second-indexed = weak-one-step-index-resultᵀ second refl
    second-transport second-coherence

  second-lineage = weak-step-store-lineage _
    (lift-store-embeddingⁱ liftρ⁺) (prefix-∷ⁱ prefix-reflⁱ)

  final-world = world-coherent-matched-allocation liftρ⁺ final-coherent

  final-exclusive⁺ =
    source-name-exclusive-matched-head final-exclusive

  final-unique⁺ =
    assumption-membership-unique-matched final-unique
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑ᵀ {q = νⁱ safe occ q}
      mode seal★ s⊑ liftρ lift-left-ctx-[] inner)
    vV noV
    with lift-left-store-result _
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑ᵀ {q = νⁱ safe occ q}
      mode seal★ s⊑ liftρ lift-left-ctx-[] inner)
    vV noV
    | ρ↑ , liftρ⁺
    with left-νcast-allocation {{safe = safe}}
      vV noV mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        seal★)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        s⊑)
      _ liftρ⁺
      (allocation-prefixᵀ prefix inner
        (ν-body-typing-at
          (proj₁ (coercion-src-tgtᵐ (proj₁ s⊑))) source⊢)
        target⊢)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (νcast⊑ᵀ {q = νⁱ safe occ q}
      mode seal★ s⊑ liftρ lift-left-ctx-[] inner)
    vV noV
    | ρ↑ , liftρ⁺ | source-step , target-refl , related =
  world-coherent-source-one-step-indexed
    (weak-indexed-result result related
      (weak-step-transport
        (left-lift-prefix-body-proofᵀ
          liftρ⁺ (prefix-∷ⁱ prefix-reflⁱ)))
      (weak-step-type-coherence source-lift-arrowᵢ source-lift-allᵢ))
    (weak-step-store-lineage ρ↑
      (lift-left-store-embeddingⁱ liftρ⁺)
      (prefix-∷ⁱ prefix-reflⁱ))
    refl refl
    (world-coherent-left-allocation liftρ⁺ coherent)
    (source-name-exclusive-source-only-head exclusive)
    (assumption-membership-unique-source unique)
  where
  result : WeakOneStepResult _ _ _ _ _ keep
  result =
    record
      { sourceChanges = bind _ ∷ []
      ; targetTailChanges = []
      ; sourceResult = _
      ; targetResult = _
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
      ; resultLeftCtx = suc _
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = store-left zero ★ _ ∷ ρ↑
      ; resultSourceType = ⇑ᵗ _
      ; resultTargetType = _
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-source-liftνᵢ
      ; transportAllBody = source-lift-under-∀ᵢ
      ; transportRightBody = ⊑-source-under-rightᵢ
      ; resultType = ⊑-source-liftνᵢ _
      ; sourceCatchup = ↠-step source-step ↠-refl
      ; targetTail = target-refl
      ; sourceStoreResult =
          cong ((zero , ★) ∷_) (leftStoreⁱ-lift-left liftρ⁺)
      ; targetStoreResult = rightStoreⁱ-lift-left liftρ⁺
      ; relatedResults = related
      }
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ inner q) vV noV =
  sourceStepTargetNarrowFrame
    world-coherent-source-one-step-target-cast-frames
    prefix mode′ seal★′ c′⊒
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊒))) target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ inner q) vV noV =
  sourceStepTargetWidenFrame
    world-coherent-source-one-step-target-cast-frames
    prefix mode′ seal★′ c′⊑
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑cast⊑idᵀ seal★′ c′⊑ inner q) vV noV =
  sourceStepTargetIdWidenFrame
    world-coherent-source-one-step-target-cast-frames
    prefix seal★′ c′⊑
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ c′⊑))) target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↑ᵀ c′↑ inner q) vV noV =
  sourceStepTargetRevealFrame
    world-coherent-source-one-step-target-cast-frames prefix c′↑
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing c′↑))))
        target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑conv↓ᵀ c′↓ inner q) vV noV =
  sourceStepTargetConcealFrame
    world-coherent-source-one-step-target-cast-frames prefix c′↓
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (cast-runtime ok-target) source⊢
      (cast-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↓⇒coercion
            (conceal-conversion-typing c′↓)))) target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑νᵀ hA h⇑A s↑ liftρ lift-right-ctx-[] r inner) vV noV =
  sourceStepTargetNuFrame
    world-coherent-source-one-step-target-nu-framesᵀ
    prefix hA s↑ r
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (ν-runtime ok-target) source⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ
          (conversion↑⇒coercion (reveal-conversion-typing s↑))))
        target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑νcastᵀ mode seal★ s⊑ liftρ lift-right-ctx-[] r inner)
    vV noV =
  sourceStepTargetNuCastFrame
    world-coherent-source-one-step-target-nu-framesᵀ
    prefix mode seal★ s⊑ r
    (world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
      ok-source (ν-runtime ok-target) source⊢
      (ν-body-typing-at
        (proj₁ (coercion-src-tgtᵐ (proj₁ s⊑))) target⊢)
      inner vV noV)
world-coherent-source-allocation-step-proofᵀ
    right-catchup paired-steps target-bullet prefix coherent exclusive unique
      wfL wfR
    ok-source ok-target source⊢ target⊢
    (⊑αᵀ vL′ noL′ h⇑A liftρ lift-right-ctx-[] inner r
      inner-source⊢ inner-target⊢)
    vV noV =
  target-bullet h⇑A prefix coherent exclusive unique wfL wfR
    ok-source ok-target source⊢ target⊢ vL′ noL′ liftρ inner
    inner-source⊢ inner-target⊢ vV noV
