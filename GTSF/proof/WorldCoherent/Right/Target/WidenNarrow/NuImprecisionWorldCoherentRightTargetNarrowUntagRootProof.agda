module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootProof
  where

-- File Charter:
--   * Proves the conditional higher-order fit of the right-target narrowing
--     untag-root resume theorem.
--   * Cancels the final target tag at the exact transported precision index,
--     then appends the target-side `tag-untag-ok` step.
--   * Takes the reopened target-tag cancellation contract explicitly; its
--     canonical assembly waits for the cancellation implementation.
--   * Reuses the existing complete world-coherent right-value catch-up
--     carrier and introduces no result, outcome, view, path, or alias.
--   * Contains only total proof definitions and explicit clauses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

import Coercions as C
open import CastImprecisionShape using
  (narrowing; _⊢ᶜ_⦂_)
open import Coercions using (ModeEnv; _!; _？)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  (narrow-weaken; _∣_∣_⊢_∶_⊒_)
import NarrowWiden as NW
open import NuReduction using
  ( StoreChange
  ; applyStore
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; tag-untag-ok
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; no•-⟨⟩; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; forget; _∣_∣_⊢_⦂_)
open import Types using
  (Ground; Ty; TyCtx; ★; ★⇒★; ＇_; ‵_; ⇑ᵗ)
open import proof.DGG.Core.NuProgress using
  (StarView; canonical-★; sv-tag)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
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
  ( apply-narrows-typing
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst²-to-≅
  ; weak-one-step-compose-preserves-type-coherenceᵀ
  ; weak-one-step-compose-preserves-transportᵀ
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-composeᵀ
  ; weak-one-step-index-resultᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTransport
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
  ; transportNo•Terms
  ; transportShapeCoherent
  ; transportType
  ; weak-step-transport
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion; store-imp-prefix-transⁱ)
open import proof.Target.SealTag.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)
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
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyTerms-++
  ; applyTyUnderTyBinder
  ; applyTyVars-++
  ; applyTys-++
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.OneStep.NuImprecisionOneStepRelated using
  ( weak-one-step-related-transportᵀ
  ; weak-one-step-related-type-coherenceᵀ
  ; weak-one-step-relatedᵀ
  )


private
  applyTy-preserves-Ground :
    ∀ χ {G} →
    Ground G →
    Ground (applyTy χ G)
  applyTy-preserves-Ground keep gG = gG
  applyTy-preserves-Ground (bind A) (＇ α) = ＇ (suc α)
  applyTy-preserves-Ground (bind A) (‵ ι) = ‵ ι
  applyTy-preserves-Ground (bind A) ★⇒★ = ★⇒★

  applyTys-preserves-Ground :
    ∀ χs {G} →
    Ground G →
    Ground (applyTys χs G)
  applyTys-preserves-Ground [] gG = gG
  applyTys-preserves-Ground (χ ∷ χs) gG =
    applyTys-preserves-Ground χs (applyTy-preserves-Ground χ gG)

  applyTys-star :
    ∀ χs →
    applyTys χs ★ ≡ ★
  applyTys-star [] = refl
  applyTys-star (keep ∷ χs) = applyTys-star χs
  applyTys-star (bind A ∷ χs) = applyTys-star χs

  applyCoercions-untag :
    ∀ χs H →
    applyCoercions χs (H C.？) ≡ applyTys χs H C.？
  applyCoercions-untag [] H = refl
  applyCoercions-untag (keep ∷ χs) H =
    applyCoercions-untag χs H
  applyCoercions-untag (bind A ∷ χs) H =
    applyCoercions-untag χs (⇑ᵗ H)

  canonical-applied-target-star :
    ∀ {Δ Σ V A} →
    A ≡ ★ →
    Value V →
    Δ ∣ Σ ∣ [] ⊢ V ⦂ A →
    StarView V
  canonical-applied-target-star refl vV V⊢ =
    canonical-★ vV (forget V⊢)

  tag-no•⁻¹ :
    ∀ {V G} →
    No• (V ⟨ G C.! ⟩) →
    No• V
  tag-no•⁻¹ (no•-⟨⟩ noV) = noV

  post-catchup-tag-untag :
    ∀ χs {V G H} →
    Value V →
    G ≡ applyTys χs H →
    V ⟨ G C.! ⟩ ⟨ applyCoercions χs (H C.？) ⟩ —→[ keep ] V
  post-catchup-tag-untag χs {H = H} vV refl
      rewrite applyCoercions-untag χs H =
    pure-step (tag-untag-ok vV)

  narrow-untag-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A H : Ty} {μ : ModeEnv}
      {s : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ H C.？ ∶ ★ ⊒ H →
    narrowing ⊢ᶜ H C.？ ⦂ s →
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
           ⟨ applyCoercions (targetTailChanges inner) (H C.？) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) H
       ∶ transportType inner q)
  narrow-untag-framed-relation
      {Δᴿ = Δᴿ} {H = H} {p = p} {q = q}
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
  narrow-untag-framed-relation
      {Δᴿ = Δᴿ} {H = H} {p = p} {q = q}
      prefix mode seal★ c⊒ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊒ =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      final-c-shape final-comp
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    final-seal :
      SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
    final-seal =
      subst (SealModeStore★ μ″)
        (sym (targetStoreResult inner)) seal★″

    final-cast :
      μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (H C.？)
          ∶ applyTys (targetTailChanges inner) ★
            ⊒ applyTys (targetTailChanges inner) H
    final-cast =
      subst
        (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (H C.？)
            ∶ applyTys (targetTailChanges inner) ★
              ⊒ applyTys (targetTailChanges inner) H)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → μ″
            ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner) (H C.？)
              ∶ applyTys (targetTailChanges inner) ★
                ⊒ applyTys (targetTailChanges inner) H)
          (sym (targetStoreResult inner)) c″⊒)

    final-c-shape =
      cast-shape-applyCoercions
        (targetTailChanges inner) c-shape

    final-comp =
      imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        comp

  target-untag-resume-core :
    TargetTagCancellationᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A H : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
    Ground H →
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
           ⟨ applyCoercions (targetTailChanges inner) (H C.？) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) H
       ∶ transportType inner q) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ H C.？ ⟩} {ρ = ρ⁺} q
  target-untag-resume-core cancel {A = A} {H = H} {q = q} gH
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      framed-relation
      with canonical-applied-target-star
        (applyTys-star
          (targetTailChanges
            (weakIndexedResult (rightCatchupIndexedResult catchup))))
        (rightCatchupTargetValue catchup)
        (nu-term-imprecision-target-typing
          (canonicalIndexedResults (rightCatchupIndexedResult catchup)))
  target-untag-resume-core cancel {A = A} {H = H} {q = q} gH
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      framed-relation
      | sv-tag {W = W} {G = G} vW refl
      with cancel final-exclusive
        final-unique
        (applyTys-preserves-Ground
          (targetTailChanges
            (weakIndexedResult (rightCatchupIndexedResult catchup))) gH)
        (subst Value
          (sym (rightCatchupSourceUnchanged catchup))
          (rightCatchupSourceValue catchup))
        (subst No•
          (sym (rightCatchupSourceUnchanged catchup))
          (rightCatchupSourceNoBullet catchup))
        vW
        (nu-term-imprecision-transport-typesᵀ
          refl
          (applyTys-star
            (targetTailChanges
              (weakIndexedResult (rightCatchupIndexedResult catchup))))
          refl
          (canonicalIndexedResults (rightCatchupIndexedResult catchup)))
        (transportType
          (weakIndexedResult (rightCatchupIndexedResult catchup)) q)
  target-untag-resume-core cancel {A = A} {H = H} {q = q} gH
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      framed-relation
      | sv-tag {W = W} {G = G} vW refl
      | tag-eq , canceled =
    world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-one-step-index-resultᵀ combined type-eq
          combined-transport combined-coherence)
        combined-source-empty
        combined-source-unchanged
        (rightCatchupSourceValue catchup)
        (rightCatchupSourceNoBullet catchup)
        vW
        noW)
      combined-lineage
      combined-bullet
      final-world
      final-exclusive
      final-unique
      final-wfR
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed
    χs = targetTailChanges inner

    first =
      weak-one-step-target-cast-frameᵀ
        {B′ = H} {c = H C.？} {χ = keep} {q = q}
        inner framed-relation

    target-step = post-catchup-tag-untag χs vW tag-eq

    second = weak-one-step-relatedᵀ canceled

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
      cong (λ χs′ → χs′ ++ [])
        (rightCatchupSourceChangesEmpty catchup)

    combined-source-unchanged :
      sourceResult combined ≡ _
    combined-source-unchanged =
      rightCatchupSourceUnchanged catchup

    noW : No• W
    noW = tag-no•⁻¹ (rightCatchupTargetNoBullet catchup)

    first-transport =
      weak-one-step-target-cast-frame-transportᵀ
        inner framed-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

    first-coherence =
      weak-one-step-target-cast-frame-coherenceᵀ
        inner framed-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

    second-transport =
      weak-one-step-related-transportᵀ canceled

    second-coherence =
      weak-one-step-related-type-coherenceᵀ canceled

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


right-target-narrow-untag-root-proofᵀ :
  TargetTagCancellationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A H : Ty} {μ : ModeEnv}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ H C.？ ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ H C.？ ∶ ★ ⊒ H →
  narrowing ⊢ᶜ H C.？ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ★ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ H C.？ ⟩} {ρ = ρ⁺} q
right-target-narrow-untag-root-proofᵀ cancel
    prefix coherent exclusive unique wfR runtime vV noV mode seal★
    c⊒@(C.cast-untag hH gH ok , NW.untag gH′)
    c-shape comp V⊑M′ inner-world =
  target-untag-resume-core cancel gH inner-world
    (narrow-untag-framed-relation
      prefix mode seal★ c⊒ c-shape comp inner-world)
