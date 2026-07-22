module
  proof.NuImprecisionWorldCoherentRightTargetActiveUnsealRootProof
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

import Coercions as C
open import Coercions using (ModeEnv; unseal)
open import Conversion using
  (RevealConversion; reveal-unseal; weaken-reveal-conversion)
open import Imprecision using (_ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
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
open import proof.NuProgress using (SealView; canonical-＇; sv-seal)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  ; rel-store-embedding-reflⁱ
  )
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  ; rightCatchupTransport
  ; rightCatchupTypeCoherence
  )
open import
  proof.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( apply-reveal-conversions
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst²-to-≅
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; weak-one-step-compose-all-body
  ; weak-one-step-compose-all-componentsᵀ
  ; weak-one-step-compose-arrow-componentsᵀ
  ; weak-one-step-compose-preserves-transportᵀ
  ; weak-one-step-compose-type
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-composeᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  )
open import proof.NuImprecisionSimulationResultDef using
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
  ; transportType
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  )
open import proof.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion; store-imp-prefix-transⁱ)
open import proof.NuImprecisionTargetSealCancellationLemma using
  (target-seal-cancellationᵀ)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; world-coherent-right-value-indexed-catchup
  )
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuWideningTransport using (apply-widens-typing)
open import proof.ReductionProperties using
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
open import proof.StoreProperties using (∈-renameStoreᵗ)
open import proof.TypePreservation using (seal★-weaken)
open import proof.NuImprecisionOneStepRelated using
  ( weak-one-step-related-transportᵀ
  ; weak-one-step-related-type-coherenceᵀ
  ; weak-one-step-relatedᵀ
  )


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
      {χ = χ} first {χ′ = χ′} target→ second
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

  weak-one-step-compose-preserves-type-coherenceᵀ :
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
  weak-one-step-compose-preserves-type-coherenceᵀ
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
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
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

  widen-unseal-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
      ⊢ C.unseal α B ∶ ＇ α ⊑ B →
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
      {q = q} prefix mode seal★ c⊑
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
      {q = q} prefix mode seal★ c⊑
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊑ =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
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
      {q = q} prefix c↑
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-reveal-conversions
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↑)
  reveal-unseal-framed-relation {Δᴿ = Δᴿ} {B = B} {α = α}
      {q = q} prefix c↑
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , β″ , X″ , c″↑ =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    final-conversion :
      RevealConversion μ″ (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner)) β″ X″
        (applyCoercions (targetTailChanges inner) (C.unseal α B))
        (applyTys (targetTailChanges inner) (＇ α))
        (applyTys (targetTailChanges inner) B)
    final-conversion =
      subst
        (λ Δ → RevealConversion μ″ Δ
          (rightStoreⁱ (resultStore inner)) β″ X″
          (applyCoercions (targetTailChanges inner) (C.unseal α B))
          (applyTys (targetTailChanges inner) (＇ α))
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion μ″
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ β″ X″
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
        (weak-one-step-index-resultᵀ combined type-eq)
        combined-source-empty
        combined-source-unchanged
        (rightCatchupSourceValue catchup)
        (rightCatchupSourceNoBullet catchup)
        vW
        noW
        combined-transport
        combined-coherence)
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
        inner framed-relation (rightCatchupTransport catchup)

    first-coherence =
      weak-one-step-target-cast-frame-coherenceᵀ
        inner framed-relation (rightCatchupTypeCoherence catchup)

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
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q
rightTargetWidenUnsealRoot {B = B} {α = α}
    prefix coherent exclusive unique wfR okUnseal vV noV mode seal★
    c⊑@(C.cast-unseal hB αB∈Σ ok , NW.unsealʷ .α .B)
    V⊑M′ inner-world =
  target-unseal-resume-core prefix inner-world αB∈Σ
    (widen-unseal-framed-relation prefix mode seal★ c⊑ inner-world)


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
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q
rightTargetRevealUnsealRoot
    prefix coherent exclusive unique wfR okUnseal vV noV
    c↑@(reveal-unseal hB αB∈Σ ok)
    V⊑M′ inner-world =
  target-unseal-resume-core prefix inner-world αB∈Σ
    (reveal-unseal-framed-relation prefix c↑ inner-world)
