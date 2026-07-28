module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetActiveRootResumeProof
  where

-- File Charter:
--   * Proves the five standalone right-target active identity-root resume
--     theorems for narrow, widen, id-only widen, reveal, and conceal roots.
--   * Appends the target-side post-catch-up `β-id` step to an already
--     completed inner right-value catch-up.
--   * Reuses the existing complete world-coherent right-value catch-up
--     carrier and preserves transport, type coherence, store lineage,
--     source-bullet transport, and final-world evidence.
--   * Does not assemble the full active-root record or attempt non-identity
--     roots.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

import Coercions as C
import Conversion as Conv
import CastImprecisionShape as CastShape
open import Coercions using
  (ModeEnv; id; id-onlyᵈ; id-only≤tag-or-idᵈ)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Imprecision using (_ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-mode-relax
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
import NarrowWiden as NW
open import NuReduction using
  ( StoreChange
  ; applyStore
  ; applyStores
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; β-id
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ; seal★-tag-or-id)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Store using (StoreIncl-drop)
open import TermTyping using
  (CastMode; SealModeStore★; cast-tag-or-id)
open import Types using
  (Atom; Ty; TyCtx; TyVar; WfTy; ＇_; ‵_; ★; _⇒_; `∀; ⇑ᵗ)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.OneStep.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-reflⁱ
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  using (rel-store-embedding-prefix-invⁱ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst²-to-≅
  ; transport-all-⊑ᵢ
  ; transportAllType-to-raw≅
  ; transport-arrow-⊑ᵢ
  ; transportArrowType-to-raw≅
  ; weak-one-step-compose-all-body
  ; weak-one-step-compose-all-componentsᵀ
  ; weak-one-step-compose-arrow-componentsᵀ
  ; weak-one-step-compose-preserves-type-coherenceᵀ
  ; weak-one-step-compose-preserves-transportᵀ
  ; weak-one-step-compose-type
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-composeᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
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
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllBody
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportArrowType
  ; transportNo•Terms
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportType
  ; transportAllType
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion; store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-compose-store-lineageᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; world-coherent-right-value-indexed-catchup
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyStores-++
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTyVars
  ; applyTyUnderTyBinder
  ; applyTyCtxs-++
  ; applyTyVars-++
  ; applyTys-++
  ; applyTys-⇒
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.TypeProperties using (renameᵗ-id)
open import proof.OneStep.NuImprecisionOneStepRelated using
  ( weak-one-step-related-transportᵀ
  ; weak-one-step-related-type-coherenceᵀ
  ; weak-one-step-relatedᵀ
  )
open import proof.Core.Properties.NuConversionTransport
  using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )


private
  applyTy-preserves-Atom :
    ∀ χ {A} →
    Atom A →
    Atom (applyTy χ A)
  applyTy-preserves-Atom keep atom = atom
  applyTy-preserves-Atom (bind A) (＇ X) = ＇ (suc X)
  applyTy-preserves-Atom (bind A) (‵ ι) = ‵ ι
  applyTy-preserves-Atom (bind A) ★ = ★

  applyTys-preserves-Atom :
    ∀ χs {A} →
    Atom A →
    Atom (applyTys χs A)
  applyTys-preserves-Atom [] atom = atom
  applyTys-preserves-Atom (χ ∷ χs) atom =
    applyTys-preserves-Atom χs (applyTy-preserves-Atom χ atom)

  post-catchup-β-id :
    ∀ χs {V A} →
    Value V →
    V ⟨ applyCoercions χs (C.id A) ⟩ —→[ keep ] V
  post-catchup-β-id [] vV = pure-step (β-id vV)
  post-catchup-β-id (keep ∷ χs) vV =
    post-catchup-β-id χs vV
  post-catchup-β-id (bind A ∷ χs) {A = B} vV =
    post-catchup-β-id χs {A = ⇑ᵗ B} vV

  target-identity-resume-core :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (atom : Atom B) →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ C.id B ⟩} {ρ = ρ⁺} q
  target-identity-resume-core {B = B} {q = q} atom
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      framed-relation =
    world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-one-step-index-resultᵀ combined type-eq
          combined-transport combined-coherence)
        combined-source-empty
        combined-source-unchanged
        (rightCatchupSourceValue catchup)
        (rightCatchupSourceNoBullet catchup)
        (rightCatchupTargetValue catchup)
        (rightCatchupTargetNoBullet catchup))
      combined-lineage
      combined-bullet
      final-world
      final-exclusive
      final-unique
      final-wfR
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    first =
      weak-one-step-target-cast-frameᵀ
        {B′ = B} {c = C.id B} {χ = keep} {q = q}
        inner framed-relation

    final-target-atom =
      applyTys-preserves-Atom (targetTailChanges inner) atom

    second-relation =
      atomic-target-value-reindexᵀ final-target-atom
        (rightCatchupTargetValue catchup)
        (canonicalIndexedResults indexed)
        (transportType inner q)

    second = weak-one-step-relatedᵀ second-relation

    target-step =
      post-catchup-β-id
        (targetTailChanges inner) (rightCatchupTargetValue catchup)

    combined = weak-one-step-composeᵀ first target-step second

    type-eq =
      HE.≅-to-≡
        (HE.trans
          (subst²-to-≅
            {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
              ⊢ S ⊑ T ⊣ resultRightCtx combined}
            (sourceTypeResult combined)
            (targetTypeResult combined)
            (resultType combined))
          (HE.sym
            (weak-one-step-compose-type-to-nested≅
              first second q)))

    combined-source-empty :
      sourceChanges combined ≡ []
    combined-source-empty =
      cong (λ χs → χs ++ [])
        (rightCatchupSourceChangesEmpty catchup)

    combined-source-unchanged :
      sourceResult combined ≡ _
    combined-source-unchanged =
      rightCatchupSourceUnchanged catchup

    first-transport =
      weak-one-step-target-cast-frame-transportᵀ
        inner framed-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

    first-coherence =
      weak-one-step-target-cast-frame-coherenceᵀ
        inner framed-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

    second-transport =
      weak-one-step-related-transportᵀ second-relation

    second-coherence =
      weak-one-step-related-type-coherenceᵀ second-relation

    combined-transport =
      weak-one-step-compose-preserves-transportᵀ
        first target-step second first-transport second-transport

    combined-coherence =
      weak-one-step-compose-preserves-type-coherenceᵀ
        first target-step second first-coherence second-coherence

    second-lineage =
      weak-step-store-lineage
        (resultStore inner) rel-store-embedding-reflⁱ prefix-reflⁱ

    first-lineage : WeakOneStepStoreLineage first
    first-lineage =
      weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage)

    combined-lineage =
      weak-one-step-compose-store-lineageᵀ
        first target-step second first-lineage second-lineage

    combined-bullet :
      RightValueCatchupSourceBulletTransportᵀ combined
    combined-bullet =
      bullet
      where
      bullet :
        RightValueCatchupSourceBulletTransportᵀ combined
      bullet {L = L} {M′ = M′} {C = C} {C′ = C′} {q = q′}
          prefix okL noM′ L⊢ L⊑M′ =
        nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-++
            (sourceChanges inner)
            []
            ((⇑ᵗᵐ L) •)))
          (sym (applyTerms-++
            (targetTailChanges inner)
            (keep ∷ [])
            (applyTerm keep M′)))
          (nu-term-imprecision-transport-typesᵀ
            (sym (applyTys-++ (sourceChanges inner) [] C))
            (sym (applyTys-++
              (targetTailChanges inner)
              (keep ∷ [])
              (applyTy keep C′)))
            refl
            first-relation)
        where
        first-relation =
          source-bullet-transport prefix okL noM′ L⊢ L⊑M′

  narrow-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {μ : ModeEnv}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {s : ImprecisionShape} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ C.id B ∶ B ⊒ B →
    CastShape.narrowing CastShape.⊢ᶜ C.id B ⦂ s →
    ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  narrow-framed-relation {Δᴿ = Δᴿ} {B = B} {p = p} {q = q}
      prefix mode seal★ c⊒ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-narrows-typing
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊒)
  narrow-framed-relation {Δᴿ = Δᴿ} {B = B} {p = p} {q = q}
      prefix mode seal★ c⊒ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊒ =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (targetTailChanges inner)
        c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent type-coherence q)
        refl
        (transportShapeCoherent type-coherence p)
        comp)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed
    type-coherence = weakIndexedTypeCoherence indexed

    final-seal :
      SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
    final-seal =
      subst (SealModeStore★ μ″)
        (sym (targetStoreResult inner)) seal★″

    final-cast :
      μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (C.id B)
          ∶ applyTys (targetTailChanges inner) B
            ⊒ applyTys (targetTailChanges inner) B
    final-cast =
      subst
        (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (C.id B)
            ∶ applyTys (targetTailChanges inner) B
              ⊒ applyTys (targetTailChanges inner) B)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner) (C.id B)
              ∶ applyTys (targetTailChanges inner) B
                ⊒ applyTys (targetTailChanges inner) B)
          (sym (targetStoreResult inner)) c″⊒)

  widen-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {μ : ModeEnv}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {s : ImprecisionShape} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ C.id B ∶ B ⊑ B →
    CastShape.widening CastShape.⊢ᶜ C.id B ⦂ s →
    ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  widen-framed-relation {Δᴿ = Δᴿ} {B = B} {p = p} {q = q}
      prefix mode seal★ c⊑ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-widens-typing
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊑)
  widen-framed-relation {Δᴿ = Δᴿ} {B = B} {p = p} {q = q}
      prefix mode seal★ c⊑ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊑ =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (targetTailChanges inner)
        c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent type-coherence p)
        refl
        (transportShapeCoherent type-coherence q)
        comp)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed
    type-coherence = weakIndexedTypeCoherence indexed

    final-seal :
      SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
    final-seal =
      subst (SealModeStore★ μ″)
        (sym (targetStoreResult inner)) seal★″

    final-cast :
      μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (C.id B)
          ∶ applyTys (targetTailChanges inner) B
            ⊑ applyTys (targetTailChanges inner) B
    final-cast =
      subst
        (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (C.id B)
            ∶ applyTys (targetTailChanges inner) B
              ⊑ applyTys (targetTailChanges inner) B)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner) (C.id B)
              ∶ applyTys (targetTailChanges inner) B
                ⊑ applyTys (targetTailChanges inner) B)
          (sym (targetStoreResult inner)) c″⊑)

  id-widen-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {s : ImprecisionShape} →
    StoreImpPrefix ρ₀ ρ⁺ →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ C.id B ∶ B ⊑ B →
    CastShape.widening CastShape.⊢ᶜ C.id B ⦂ s →
    ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  id-widen-framed-relation {Δᴿ = Δᴿ} {B = B} {p = p} {q = q}
      prefix c⊑ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR) =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ final-cast)
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (targetTailChanges inner)
        c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent type-coherence p)
        refl
        (transportShapeCoherent type-coherence q)
        comp)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed
    type-coherence = weakIndexedTypeCoherence indexed

    c″⊑ =
      apply-fixed-widens-typing
        {χs = keep ∷ targetTailChanges inner}
        (modeRename-id-only suc)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊑)

    final-cast :
      id-onlyᵈ ∣ resultRightCtx inner
        ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (C.id B)
          ∶ applyTys (targetTailChanges inner) B
            ⊑ applyTys (targetTailChanges inner) B
    final-cast =
      subst
        (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (C.id B)
            ∶ applyTys (targetTailChanges inner) B
              ⊑ applyTys (targetTailChanges inner) B)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → id-onlyᵈ
            ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner) (C.id B)
              ∶ applyTys (targetTailChanges inner) B
                ⊑ applyTys (targetTailChanges inner) B)
          (sym (targetStoreResult inner)) c″⊑)

  reveal-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X (C.id B) B B →
    p [ β ↦ X ]ᴿ q →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  reveal-framed-relation {Δᴿ = Δᴿ} {B = B} {X = X} {β = β} {q = q}
      prefix c↑ replacement
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-reveal-conversions-exact
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↑)
  reveal-framed-relation {Δᴿ = Δᴿ} {B = B} {X = X} {β = β} {q = q}
      prefix c↑ replacement
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , c″↑ =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    final-conversion :
      RevealConversion μ″ (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) (C.id B))
        (applyTys (targetTailChanges inner) B)
        (applyTys (targetTailChanges inner) B)
    final-conversion =
      subst
        (λ Δ → RevealConversion μ″ Δ
          (rightStoreⁱ (resultStore inner))
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) (C.id B))
          (applyTys (targetTailChanges inner) B)
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion μ″
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
            (applyTyVars (targetTailChanges inner) β)
            (applyTys (targetTailChanges inner) X)
            (applyCoercions (targetTailChanges inner) (C.id B))
            (applyTys (targetTailChanges inner) B)
            (applyTys (targetTailChanges inner) B))
          (sym (targetStoreResult inner)) c″↑)

  conceal-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X
      (C.id B) B B →
    q [ β ↦ X ]ᴿ p →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  conceal-framed-relation {Δᴿ = Δᴿ} {B = B} {X = X} {β = β} {q = q}
      prefix c↓ replacement
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-conceal-conversions-exact
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        (weaken-conceal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↓)
  conceal-framed-relation {Δᴿ = Δᴿ} {B = B} {X = X} {β = β} {q = q}
      prefix c↓ replacement
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , c″↓ =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed) replacement)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    final-conversion :
      ConcealConversion μ″ (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) (C.id B))
        (applyTys (targetTailChanges inner) B)
        (applyTys (targetTailChanges inner) B)
    final-conversion =
      subst
        (λ Δ → ConcealConversion μ″ Δ
          (rightStoreⁱ (resultStore inner))
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) (C.id B))
          (applyTys (targetTailChanges inner) B)
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → ConcealConversion μ″
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
            (applyTyVars (targetTailChanges inner) β)
            (applyTys (targetTailChanges inner) X)
            (applyCoercions (targetTailChanges inner) (C.id B))
            (applyTys (targetTailChanges inner) B)
            (applyTys (targetTailChanges inner) B))
          (sym (targetStoreResult inner)) c″↓)


rightTargetNarrowIdentityRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty} {μ : ModeEnv}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {s : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ id B ∶ B ⊒ B →
  CastShape.narrowing CastShape.⊢ᶜ id B ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q
rightTargetNarrowIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.cross (NW.id-＇ α)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (＇ α) inner-world
    (narrow-framed-relation prefix mode seal★ c⊒ c-shape comp inner-world)
rightTargetNarrowIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.cross (NW.id-‵ ι)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (‵ ι) inner-world
    (narrow-framed-relation prefix mode seal★ c⊒ c-shape comp inner-world)
rightTargetNarrowIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.id★) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core ★ inner-world
    (narrow-framed-relation prefix mode seal★ c⊒ c-shape comp inner-world)


rightTargetWidenIdentityRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty} {μ : ModeEnv}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {s : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ id B ∶ B ⊑ B →
  CastShape.widening CastShape.⊢ᶜ id B ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q
rightTargetWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊑@(C.cast-id _ _ , NW.cross (NW.id-＇ α)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (＇ α) inner-world
    (widen-framed-relation prefix mode seal★ c⊑ c-shape comp inner-world)
rightTargetWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊑@(C.cast-id _ _ , NW.cross (NW.id-‵ ι)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (‵ ι) inner-world
    (widen-framed-relation prefix mode seal★ c⊑ c-shape comp inner-world)
rightTargetWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV mode seal★
    c⊑@(C.cast-id _ _ , NW.id★) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core ★ inner-world
    (widen-framed-relation prefix mode seal★ c⊑ c-shape comp inner-world)


rightTargetIdWidenIdentityRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {s : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ id B ∶ B ⊑ B →
  CastShape.widening CastShape.⊢ᶜ id B ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q
rightTargetIdWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV seal★
    c⊑@(C.cast-id _ _ , NW.cross (NW.id-＇ α)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (＇ α) inner-world
    (id-widen-framed-relation prefix c⊑ c-shape comp inner-world)
rightTargetIdWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV seal★
    c⊑@(C.cast-id _ _ , NW.cross (NW.id-‵ ι)) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core (‵ ι) inner-world
    (id-widen-framed-relation prefix c⊑ c-shape comp inner-world)
rightTargetIdWidenIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV seal★
    c⊑@(C.cast-id _ _ , NW.id★) c-shape comp
    V⊑M′ inner-world =
  target-identity-resume-core ★ inner-world
    (id-widen-framed-relation prefix c⊑ c-shape comp inner-world)


rightTargetRevealIdentityRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X (id B) B B →
  p [ β ↦ X ]ᴿ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q
rightTargetRevealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↑@(Conv.reveal-id-var {Y = Y} hY ok) replacement
    V⊑M′ inner-world =
  target-identity-resume-core (＇ Y) inner-world
    (reveal-framed-relation prefix c↑ replacement inner-world)
rightTargetRevealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↑@(Conv.reveal-id-base {ι = ι}) replacement
    V⊑M′ inner-world =
  target-identity-resume-core (‵ ι) inner-world
    (reveal-framed-relation prefix c↑ replacement inner-world)
rightTargetRevealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↑@Conv.reveal-id-★ replacement
    V⊑M′ inner-world =
  target-identity-resume-core ★ inner-world
    (reveal-framed-relation prefix c↑ replacement inner-world)


rightTargetConcealIdentityRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X (id B) B B →
  q [ β ↦ X ]ᴿ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q
rightTargetConcealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↓@(Conv.conceal-id-var {Y = Y} hY ok) replacement
    V⊑M′ inner-world =
  target-identity-resume-core (＇ Y) inner-world
    (conceal-framed-relation prefix c↓ replacement inner-world)
rightTargetConcealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↓@(Conv.conceal-id-base {ι = ι}) replacement
    V⊑M′ inner-world =
  target-identity-resume-core (‵ ι) inner-world
    (conceal-framed-relation prefix c↓ replacement inner-world)
rightTargetConcealIdentityRoot
    prefix coherent exclusive unique wfR okId vV noV
    c↓@Conv.conceal-id-★ replacement
    V⊑M′ inner-world =
  target-identity-resume-core ★ inner-world
    (conceal-framed-relation prefix c↓ replacement inner-world)
