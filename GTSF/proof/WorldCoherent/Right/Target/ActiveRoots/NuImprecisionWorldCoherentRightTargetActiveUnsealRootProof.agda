module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetActiveUnsealRootProof
  where

-- File Charter:
--   * Proves the two standalone right-target active unseal-root resume
--     theorems for widening and reveal roots.
--   * Appends the target-side post-catch-up `seal-unseal` step to an already
--     completed inner right-value catch-up.
--   * Reuses target seal cancellation and the complete world-coherent
--     right-value catch-up carrier without introducing a new result, outcome,
--     view, path, or alias.
--   * Contains only total proof definitions and explicit clauses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

import CastImprecisionShape as CastShape
import Coercions as C
open import Coercions using (ModeEnv; unseal)
open import Conversion using
  (RevealConversion; reveal-unseal; weaken-reveal-conversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Imprecision using (_ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  (widen-weaken; _∣_∣_⊢_∶_⊑_)
import NarrowWiden as NW
open import NuReduction using
  ( StoreChange
  ; applyStore
  ; applyStores
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; seal-unseal
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
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; forget; _∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; TyVar; ＇_; ⇑ᵗ; _⇒_; `∀)
open import proof.DGG.Core.NuProgress using (SealView; canonical-＇; sv-seal)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  ; rel-store-embedding-reflⁱ
  )
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
  ; transportAllType-to-raw≅
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
  ; transportAllType
  ; transportArrowCoherent
  ; transportArrowType
  ; transportNo•Terms
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportType
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion; store-imp-prefix-transⁱ)
open import proof.Target.SealTag.NuImprecisionTargetSealCancellationLemma using
  (target-seal-cancellationᵀ)
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
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  using (weak-one-step-compose-type-preserves-shapeᵀ)
open import proof.Core.Properties.NuWideningTransport using (apply-widens-typing)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyStores-++
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTerm-preserves-No•
  ; applyTyUnderTyBinder
  ; applyTyVars
  ; applyTyVars-++
  ; applyTys-++
  ; applyTysUnderTyBinders-++
  )
open import proof.Core.Properties.StoreProperties using (∈-renameStoreᵗ)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.OneStep.NuImprecisionOneStepRelated using
  ( weak-one-step-related-transportᵀ
  ; weak-one-step-related-type-coherenceᵀ
  ; weak-one-step-relatedᵀ
  )
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedConversionTransportProof
  using (apply-reveal-conversions-exact)


private
  applyTys-var :
    ∀ χs α →
    applyTys χs (＇ α) ≡ ＇ (applyTyVars χs α)
  applyTys-var [] α = refl
  applyTys-var (keep ∷ χs) α = applyTys-var χs α
  applyTys-var (bind A ∷ χs) α = applyTys-var χs (suc α)

  applyCoercions-unseal :
    ∀ χs α A →
    applyCoercions χs (C.unseal α A) ≡
      C.unseal (applyTyVars χs α) (applyTys χs A)
  applyCoercions-unseal [] α A = refl
  applyCoercions-unseal (keep ∷ χs) α A =
    applyCoercions-unseal χs α A
  applyCoercions-unseal (bind B ∷ χs) α A =
    applyCoercions-unseal χs (suc α) (⇑ᵗ A)

  applyStores-member :
    ∀ χs {Σ α A} →
    (α , A) ∈ Σ →
    (applyTyVars χs α , applyTys χs A) ∈ applyStores χs Σ
  applyStores-member [] x∈ = x∈
  applyStores-member (keep ∷ χs) x∈ =
    applyStores-member χs x∈
  applyStores-member (bind B ∷ χs) x∈ =
    applyStores-member χs (there (∈-renameStoreᵗ suc x∈))

  canonical-applied-target-var :
    ∀ {Δ Σ V A α} →
    A ≡ ＇ α →
    Value V →
    Δ ∣ Σ ∣ [] ⊢ V ⦂ A →
    SealView {α = α} V
  canonical-applied-target-var refl vV V⊢ =
    canonical-＇ vV (forget V⊢)

  seal-no•⁻¹ :
    ∀ {V A α} →
    No• (V ⟨ C.seal A α ⟩) →
    No• V
  seal-no•⁻¹ (no•-⟨⟩ noV) = noV

  post-catchup-seal-unseal :
    ∀ χs {V α A B} →
    Value V →
    V ⟨ C.seal A (applyTyVars χs α) ⟩
      ⟨ applyCoercions χs (C.unseal α B) ⟩ —→[ keep ] V
  post-catchup-seal-unseal χs {α = α} {B = B} vV
      rewrite applyCoercions-unseal χs α B =
    pure-step (seal-unseal vV)

  cancel-applied-target-seal :
    ∀ {Φ Δᴸ Δᴿ W V A B D X Y α}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    B ≡ ＇ α →
    D ≡ X →
    WorldCoherent ρ →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    Value W →
    No• W →
    Value V →
    (α , X) ∈ rightStoreⁱ ρ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ W ⊑ V ⟨ C.seal Y α ⟩ ⦂ A ⊑ B ∶ p →
    (q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ W ⊑ V ⦂ A ⊑ D ∶ q
  cancel-applied-target-seal refl refl coherent wfR vW noW vV
      αX∈Σ W⊑V q =
    target-seal-cancellationᵀ coherent wfR vW noW vV αX∈Σ W⊑V q

  widen-unseal-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
      {s : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
      ⊢ C.unseal α B ∶ ＇ α ⊑ B →
    CastShape.widening CastShape.⊢ᶜ C.unseal α B ⦂ s →
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
           ⟨ applyCoercions (targetTailChanges inner)
             (C.unseal α B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  widen-unseal-framed-relation {Δᴿ = Δᴿ} {B = B} {α = α}
      {p = p} {q = q} prefix mode seal★ c⊑ c-shape comp
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
  widen-unseal-framed-relation {Δᴿ = Δᴿ} {B = B} {α = α}
      {p = p} {q = q} prefix mode seal★ c⊑ c-shape comp
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊑ =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (targetTailChanges inner) c-shape)
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
        ⊢ applyCoercions (targetTailChanges inner) (C.unseal α B)
          ∶ applyTys (targetTailChanges inner) (＇ α)
            ⊑ applyTys (targetTailChanges inner) B
    final-cast =
      subst
        (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (C.unseal α B)
            ∶ applyTys (targetTailChanges inner) (＇ α)
              ⊑ applyTys (targetTailChanges inner) B)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → μ″
            ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner) (C.unseal α B)
              ∶ applyTys (targetTailChanges inner) (＇ α)
                ⊑ applyTys (targetTailChanges inner) B)
          (sym (targetStoreResult inner)) c″⊑)

  reveal-unseal-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
      α B (C.unseal α B) (＇ α) B →
    p [ α ↦ B ]ᴿ q →
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
           ⟨ applyCoercions (targetTailChanges inner)
             (C.unseal α B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  reveal-unseal-framed-relation {Δᴿ = Δᴿ} {B = B} {α = α}
      {p = p} {q = q} prefix c↑ replacement
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-reveal-conversions-exact
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↑)
  reveal-unseal-framed-relation {Δᴿ = Δᴿ} {B = B} {α = α}
      {p = p} {q = q} prefix c↑ replacement
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
        (applyTyVars (targetTailChanges inner) α)
        (applyTys (targetTailChanges inner) B)
        (applyCoercions (targetTailChanges inner) (C.unseal α B))
        (applyTys (targetTailChanges inner) (＇ α))
        (applyTys (targetTailChanges inner) B)
    final-conversion =
      subst
        (λ Δ → RevealConversion μ″ Δ
          (rightStoreⁱ (resultStore inner))
          (applyTyVars (targetTailChanges inner) α)
          (applyTys (targetTailChanges inner) B)
          (applyCoercions (targetTailChanges inner) (C.unseal α B))
          (applyTys (targetTailChanges inner) (＇ α))
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion μ″
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
            (applyTyVars (targetTailChanges inner) α)
            (applyTys (targetTailChanges inner) B)
            (applyCoercions (targetTailChanges inner) (C.unseal α B))
            (applyTys (targetTailChanges inner) (＇ α))
            (applyTys (targetTailChanges inner) B))
          (sym (targetStoreResult inner)) c″↑)

  target-unseal-resume-core :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {α : TyVar}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (α , B) ∈ rightStoreⁱ ρ₀ →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner)
             (C.unseal α B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ C.unseal α B ⟩} {ρ = ρ⁺} q
  target-unseal-resume-core {A = A} {B = B} {α = α} {q = q}
      prefix
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      αB∈Σ framed-relation
      with canonical-applied-target-var
        (applyTys-var
          (targetTailChanges
            (weakIndexedResult (rightCatchupIndexedResult catchup))) α)
        (rightCatchupTargetValue catchup)
        (nu-term-imprecision-target-typing
          (canonicalIndexedResults (rightCatchupIndexedResult catchup)))
  target-unseal-resume-core {A = A} {B = B} {α = α} {q = q}
      prefix
      (world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet-transport final-world
        final-exclusive final-unique final-wfR)
      αB∈Σ framed-relation
      | sv-seal {W = W} {A = Y} vW refl =
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
        {B′ = B} {c = C.unseal α B} {χ = keep} {q = q}
        inner framed-relation

    final-source-value :
      Value (sourceResult inner)
    final-source-value =
      subst Value (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup)

    final-source-no :
      No• (sourceResult inner)
    final-source-no =
      subst No• (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup)

    final-membership :
      (applyTyVars χs α , applyTys χs B) ∈
        rightStoreⁱ (resultStore inner)
    final-membership =
      subst
        (λ Σ → (applyTyVars χs α , applyTys χs B) ∈ Σ)
        (sym (targetStoreResult inner))
        (applyStores-member χs
          (rightStoreⁱ-prefix-inclusion prefix αB∈Σ))

    canceled :
      resultCtx inner
        ∣ resultLeftCtx inner
        ∣ resultRightCtx inner
        ∣ resultStore inner ∣ []
        ⊢ᴺ sourceResult inner ⊑ W
        ⦂ applyTys (sourceChanges inner) A
          ⊑ applyTys (targetTailChanges inner) B
        ∶ transportType inner q
    canceled =
      cancel-applied-target-seal (applyTys-var χs α) refl
        final-world final-wfR final-source-value final-source-no
        vW final-membership (canonicalIndexedResults indexed)
        (transportType inner q)

    target-step =
      post-catchup-seal-unseal χs {α = α} {A = Y} {B = B} vW

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
    noW = seal-no•⁻¹ (rightCatchupTargetNoBullet catchup)

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
          prefix′ okL noM′ L⊢ L⊑M′ =
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
          source-bullet-transport prefix′ okL noM′ L⊢ L⊑M′


rightTargetWidenUnsealRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ unseal α B ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ unseal α B ∶ ＇ α ⊑ B →
  CastShape.widening CastShape.⊢ᶜ unseal α B ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q
rightTargetWidenUnsealRoot {B = B} {α = α}
    prefix coherent exclusive unique wfR okUnseal vV noV mode seal★
    c⊑@(C.cast-unseal hB αB∈Σ ok , NW.unsealʷ .α .B) c-shape comp
    V⊑M′ inner-world =
  target-unseal-resume-core prefix inner-world αB∈Σ
    (widen-unseal-framed-relation
      prefix mode seal★ c⊑ c-shape comp inner-world)


rightTargetRevealUnsealRoot :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ unseal α B ⟩) →
  Value V →
  No• V →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    α B (unseal α B) (＇ α) B →
  p [ α ↦ B ]ᴿ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q
rightTargetRevealUnsealRoot
    prefix coherent exclusive unique wfR okUnseal vV noV
    c↑@(reveal-unseal hB αB∈Σ ok) replacement
    V⊑M′ inner-world =
  target-unseal-resume-core prefix inner-world αB∈Σ
    (reveal-unseal-framed-relation prefix c↑ replacement inner-world)
