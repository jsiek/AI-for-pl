module
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectProof
  where

-- File Charter:
--   * Implements direct source-delta scheduling against a target primitive.
--   * Catches up the target operands from left to right, then composes their
--     source-silent traces with the synchronized natural-addition delta.
--   * Contains no dispatcher recursion, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import ImprecisionWf using (idι; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightCtxⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; _∣_∣_⊢_⦂_
  ; no•-$
  ; no•-⊕
  ; ok-no
  ; ok-⊕₁
  ; ok-⊕₂
  ; $
  ; _⊕[_]_
  )
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; κ⊑κᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (`ℕ; ‵_)
open import TermTyping using (forget)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( RightValueCatchupIndexedResult
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-one-step-index-resultᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetResult
  ; targetTypeResult
  ; transportAllBody
  ; transportArrowCoherent
  ; transportNo•Terms
  ; transportRightBody
  ; transportAllCoherent
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Source.OneStep.NuImprecisionSourceOneStepDeltaRootDef using
  (WorldCoherentSourceDeltaRootᵀ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.Source.Core.NuImprecisionSourceSilentCompositionDef using
  ( SourceSilentComposition
  ; sourceSilentAssumptionMembershipUnique
  ; sourceSilentChangesExact
  ; sourceSilentResult
  ; sourceSilentResultExact
  ; sourceSilentSourceNameExclusive
  ; sourceSilentStoreLineage
  ; sourceSilentTransport
  ; sourceSilentTypeCoherence
  ; sourceSilentWorldCoherent
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  ; worldRightCatchupTargetStoreWf
  )
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage; weak-step-store-lineage)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectDef
  using (WorldCoherentSourcePrimitiveDeltaDirectᵀ)
open import proof.DGG.Core.NuProgress using (canonical-ℕ; nv-const)
open import proof.Core.Properties.ReductionProperties using
  ( applyTerms-const
  ; applyTerms-preserves-No•
  ; applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTys-ℕ
  ; applyTy-ℕ
  ; ⊕₁-↠
  ; ⊕₂-↠
  )
open import proof.Core.Properties.TypePreservation using (term-weaken)


private
  rightCtxⁱ-[] :
    ∀ {Φ Δᴸ Δᴿ} →
    rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} [] ≡ []
  rightCtxⁱ-[] = refl

  related-nat-constant-target-constantᵀ :
    ∀ {Φ Δᴸ Δᴿ m n} {ρ : StoreImp Φ Δᴸ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ $ (κℕ m) ⊑ $ (κℕ n)
        ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    m ≡ n
  related-nat-constant-target-constantᵀ κ⊑κᵀ = refl
  related-nat-constant-target-constantᵀ
      (allocation-prefixᵀ prefix relation source⊒ target⊒) =
    related-nat-constant-target-constantᵀ relation


related-nat-source-constant-target-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ n V} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ $ (κℕ n) ⊑ V ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  V ≡ $ (κℕ n)
related-nat-source-constant-target-valueᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {V = V} {ρ = ρ}
    value relation
    with canonical-ℕ value
      (subst
        (λ Γ → Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ V ⦂ ‵ `ℕ)
        (rightCtxⁱ-[] {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ})
        (forget (nu-term-imprecision-target-typing relation)))
related-nat-source-constant-target-valueᵀ
    {n = n} {V = V} value relation | nv-const {n = k} V≡
    rewrite V≡
          | related-nat-constant-target-constantᵀ relation =
  refl


private
  nat-imprecision-unique :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    p ≡ q
  nat-imprecision-unique refl refl idι idι = refl

  transport-idι-to-ℕ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    subst
      (λ T → Φ ∣ Δᴸ ⊢ ‵ `ℕ ⊑ T ⊣ Δᴿ)
      B≡ℕ
      (subst
        (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
        A≡ℕ p)
      ≡ idι
  transport-idι-to-ℕ refl refl idι = refl

  transport-idι-from-ℕ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    subst
      (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ)
      (sym B≡ℕ)
      (subst
        (λ S → Φ ∣ Δᴸ ⊢ S ⊑ ‵ `ℕ ⊣ Δᴿ)
        (sym A≡ℕ) idι)
      ≡ p
  transport-idι-from-ℕ refl refl idι = refl

  target-ℕ-result :
    ∀ χ χs →
    applyTys χs (applyTy χ (‵ `ℕ)) ≡ ‵ `ℕ
  target-ℕ-result χ χs =
    trans (cong (applyTys χs) (applyTy-ℕ χ)) (applyTys-ℕ χs)

  transport-term-to-ℕᵀ :
    ∀ {Φ Δᴸ Δᴿ A B ρ γ M M′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (A≡ℕ : A ≡ ‵ `ℕ) →
    (B≡ℕ : B ≡ ‵ `ℕ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
  transport-term-to-ℕᵀ {p = p} A≡ℕ B≡ℕ relation =
    nu-term-imprecision-transport-typesᵀ
      A≡ℕ B≡ℕ (transport-idι-to-ℕ A≡ℕ B≡ℕ p) relation

  delta-⊕₁-frameᵀ :
    ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    (inner : WeakOneStepIndexedResult
      {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι) →
    WeakOneStepTransport (weakIndexedResult inner) →
    WeakOneStepResult ρ
      (L ⊕[ addℕ ] M)
      (L₁′ ⊕[ addℕ ] applyTerm χ M′)
      (‵ `ℕ) (‵ `ℕ) χ
  delta-⊕₁-frameᵀ
      {L = L} {L₁′ = L₁′} {M = M} {M′ = M′} {χ = χ}
      noM noM′ M⊑M′ inner transport =
    record
      { sourceChanges = sourceChanges base
      ; targetTailChanges = targetTailChanges base
      ; sourceResult =
          sourceResult base ⊕[ addℕ ]
            applyTerms (sourceChanges base) M
      ; targetResult =
          targetResult base ⊕[ addℕ ]
            applyTerms (targetTailChanges base) (applyTerm χ M′)
      ; resultCtx = resultCtx base
      ; resultLeftCtx = resultLeftCtx base
      ; resultRightCtx = resultRightCtx base
      ; sourceCtxResult = sourceCtxResult base
      ; targetCtxResult = targetCtxResult base
      ; resultStore = resultStore base
      ; resultSourceType = ‵ `ℕ
      ; resultTargetType = ‵ `ℕ
      ; sourceTypeResult = sym source-ℕ
      ; targetTypeResult = sym target-ℕ
      ; transportType = transportType base
      ; transportAllBody = transportAllBody base
      ; transportRightBody = transportRightBody base
      ; resultType = idι
      ; sourceCatchup = ⊕₁-↠ noM (sourceCatchup base)
      ; targetTail =
          ⊕₁-↠ (applyTerm-preserves-No• χ noM′) (targetTail base)
      ; sourceStoreResult = sourceStoreResult base
      ; targetStoreResult = targetStoreResult base
      ; relatedResults = ⊕⊑⊕ᵀ left-related right-related
      }
    where
    base = weakIndexedResult inner
    source-ℕ = applyTys-ℕ (sourceChanges base)
    target-ℕ = target-ℕ-result χ (targetTailChanges base)
    left-related =
      transport-term-to-ℕᵀ
        source-ℕ target-ℕ (canonicalIndexedResults inner)
    right-related =
      transport-term-to-ℕᵀ source-ℕ target-ℕ
        (transportNo•Terms
          transport
          noM noM′ M⊑M′)

  delta-⊕₁-frame-lineageᵀ :
    ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (noM : No• M)
      (noM′ : No• M′)
      (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι)
      (inner : WeakOneStepIndexedResult
        {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι)
      (transport : WeakOneStepTransport (weakIndexedResult inner)) →
    WeakOneStepStoreLineage (weakIndexedResult inner) →
    WeakOneStepStoreLineage
      (delta-⊕₁-frameᵀ noM noM′ M⊑M′ inner transport)
  delta-⊕₁-frame-lineageᵀ noM noM′ M⊑M′ inner transport
      (weak-step-store-lineage store embedding prefix) =
    weak-step-store-lineage store embedding prefix

  delta-⊕₂-frameᵀ :
    ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    Value L →
    No• L →
    Value L′ →
    No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    (inner : WeakOneStepIndexedResult
      {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} idι) →
    WeakOneStepTransport (weakIndexedResult inner) →
    WeakOneStepResult ρ
      (L ⊕[ addℕ ] M)
      (applyTerm χ L′ ⊕[ addℕ ] M₁′)
      (‵ `ℕ) (‵ `ℕ) χ
  delta-⊕₂-frameᵀ
      {L = L} {L′ = L′} {M = M} {M₁′ = M₁′} {χ = χ}
      valueL noL valueL′ noL′ L⊑L′ inner transport =
    record
      { sourceChanges = sourceChanges base
      ; targetTailChanges = targetTailChanges base
      ; sourceResult =
          applyTerms (sourceChanges base) L ⊕[ addℕ ]
            sourceResult base
      ; targetResult =
          applyTerms (targetTailChanges base) (applyTerm χ L′)
            ⊕[ addℕ ] targetResult base
      ; resultCtx = resultCtx base
      ; resultLeftCtx = resultLeftCtx base
      ; resultRightCtx = resultRightCtx base
      ; sourceCtxResult = sourceCtxResult base
      ; targetCtxResult = targetCtxResult base
      ; resultStore = resultStore base
      ; resultSourceType = ‵ `ℕ
      ; resultTargetType = ‵ `ℕ
      ; sourceTypeResult = sym source-ℕ
      ; targetTypeResult = sym target-ℕ
      ; transportType = transportType base
      ; transportAllBody = transportAllBody base
      ; transportRightBody = transportRightBody base
      ; resultType = idι
      ; sourceCatchup = ⊕₂-↠ valueL noL (sourceCatchup base)
      ; targetTail =
          ⊕₂-↠
            (applyTerm-preserves-Value χ valueL′)
            (applyTerm-preserves-No• χ noL′)
            (targetTail base)
      ; sourceStoreResult = sourceStoreResult base
      ; targetStoreResult = targetStoreResult base
      ; relatedResults = ⊕⊑⊕ᵀ left-related right-related
      }
    where
    base = weakIndexedResult inner
    source-ℕ = applyTys-ℕ (sourceChanges base)
    target-ℕ = target-ℕ-result χ (targetTailChanges base)
    left-related =
      transport-term-to-ℕᵀ source-ℕ target-ℕ
        (transportNo•Terms
          transport
          noL noL′ L⊑L′)
    right-related =
      transport-term-to-ℕᵀ
        source-ℕ target-ℕ (canonicalIndexedResults inner)

  delta-⊕₂-frame-lineageᵀ :
    ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (valueL : Value L)
      (noL : No• L)
      (valueL′ : Value L′)
      (noL′ : No• L′)
      (L⊑L′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι)
      (inner : WeakOneStepIndexedResult
        {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} idι)
      (transport : WeakOneStepTransport (weakIndexedResult inner)) →
    WeakOneStepStoreLineage (weakIndexedResult inner) →
    WeakOneStepStoreLineage
      (delta-⊕₂-frameᵀ
        valueL noL valueL′ noL′ L⊑L′ inner transport)
  delta-⊕₂-frame-lineageᵀ
      valueL noL valueL′ noL′ L⊑L′ inner transport
      (weak-step-store-lineage store embedding prefix) =
    weak-step-store-lineage store embedding prefix


right-catchup-final-nat-relationᵀ :
  ∀ {Φ Δᴸ Δᴿ n M′} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (catchup : RightValueCatchupIndexedResult
    {V = $ (κℕ n)} {M′ = M′} {ρ = ρ} idι) →
  let result = weakIndexedResult (rightCatchupIndexedResult catchup)
  in
  resultCtx result ∣ resultLeftCtx result ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ $ (κℕ n) ⊑ targetResult result
      ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
right-catchup-final-nat-relationᵀ catchup
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
right-catchup-final-nat-relationᵀ catchup | refl | refl =
  nu-term-imprecision-transport-typesᵀ
    refl target-nat target-index (canonicalIndexedResults indexed)
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed

  target-nat = applyTys-ℕ (targetTailChanges result)

  target-index =
    transport-idι-to-ℕ refl target-nat (transportType result idι)


nat-result-type-unique :
  ∀ {Φ Δᴸ Δᴿ M M′} {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M M′ (‵ `ℕ) (‵ `ℕ) keep) →
  subst
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) (‵ `ℕ)
        ⊑ T ⊣ resultRightCtx result)
    (targetTypeResult result)
    (subst
      (λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ resultTargetType result ⊣ resultRightCtx result)
    (sourceTypeResult result)
      (resultType result))
    ≡ transportType result idι
nat-result-type-unique result =
  nat-imprecision-unique source-nat target-nat _ _
  where
  source-nat = applyTys-ℕ (sourceChanges result)

  target-nat =
    trans
      (cong (applyTys (targetTailChanges result)) (applyTy-ℕ keep))
      (applyTys-ℕ (targetTailChanges result))


finish-right-catchup-deltaᵀ :
  SourceSilentComposition →
  WorldCoherentSourceDeltaRootᵀ →
  ∀ {Φ Δᴸ Δᴿ m n R′} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherentRightValueCatchupIndexedResult
    {V = $ (κℕ n)} {M′ = R′} {ρ = ρ} idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {M′ = $ (κℕ m) ⊕[ addℕ ] R′}
    {L = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ} idι
finish-right-catchup-deltaᵀ
    composition delta {m = m} {n = n} right-world
    with related-nat-source-constant-target-valueᵀ
      (rightCatchupTargetValue right-catchup)
      (right-catchup-final-nat-relationᵀ right-catchup)
  where
  right-catchup = worldRightCatchupResult right-world
finish-right-catchup-deltaᵀ
    composition delta {m = m} {n = n} right-world
    | target-right≡
    with rightCatchupSourceChangesEmpty
           (worldRightCatchupResult right-world)
       | rightCatchupSourceUnchanged
           (worldRightCatchupResult right-world)
       | target-right≡
finish-right-catchup-deltaᵀ
    composition delta {m = m} {n = n} right-world
    | target-right≡ | refl | refl | refl =
  world-coherent-source-one-step-indexed
    combined-indexed
    combined-lineage
    combined-changes
    combined-result
    combined-world
    combined-exclusive
    combined-unique
  where
  right-catchup = worldRightCatchupResult right-world
  right-indexed = rightCatchupIndexedResult right-catchup
  right-result = weakIndexedResult right-indexed

  framed =
    delta-⊕₂-frameᵀ
      ($ (κℕ m)) no•-$ ($ (κℕ m)) no•-$ κ⊑κᵀ
      right-indexed (weakIndexedTransport (rightCatchupIndexedResult right-catchup))

  framed-transport =
    weak-step-transport
      (transportNo•Terms (weakIndexedTransport (rightCatchupIndexedResult right-catchup)))

  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent
        (weakIndexedTypeCoherence (rightCatchupIndexedResult right-catchup)))
      (transportAllCoherent
        (weakIndexedTypeCoherence (rightCatchupIndexedResult right-catchup)))

  framed-lineage : WeakOneStepStoreLineage framed
  framed-lineage =
    delta-⊕₂-frame-lineageᵀ
      ($ (κℕ m)) no•-$ ($ (κℕ m)) no•-$ κ⊑κᵀ
      right-indexed (weakIndexedTransport (rightCatchupIndexedResult right-catchup))
      (worldRightCatchupStoreLineage right-world)

  delta-world =
    delta prefix-reflⁱ
      (worldRightCatchupCoherence right-world)
      (worldRightCatchupSourceNameExclusive right-world)
      (worldRightCatchupAssumptionMembershipUnique right-world)

  target-framed≡ :
    targetResult framed ≡
      $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)
  target-framed≡ =
    cong₂ (λ L R → L ⊕[ addℕ ] R)
      (applyTerms-const (targetTailChanges right-result) (κℕ m))
      refl

  delta-world′ =
    subst
      (λ T → WorldCoherentSourceOneStepIndexedResult
        {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
        {M′ = T}
        {L = $ (κℕ (m + n))}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = keep} {ρ = resultStore framed} idι)
      (sym target-framed≡)
      delta-world

  delta-indexed = sourceStepIndexedResult delta-world′
  delta-result = weakIndexedResult delta-indexed

  combined = sourceSilentResult composition framed refl refl delta-result

  combined-transport =
    sourceSilentTransport composition framed refl refl delta-result
      framed-transport (weakIndexedTransport (sourceStepIndexedResult delta-world′))

  combined-coherence =
    sourceSilentTypeCoherence composition framed refl refl delta-result
      framed-coherence (weakIndexedTypeCoherence (sourceStepIndexedResult delta-world′))

  combined-indexed : WeakOneStepIndexedResult idι
  combined-indexed =
    weak-one-step-index-resultᵀ combined
      (nat-result-type-unique combined)
      combined-transport combined-coherence

  combined-lineage =
    sourceSilentStoreLineage composition framed refl refl delta-result
      framed-lineage
      (sourceStepStoreLineage delta-world′)

  combined-changes =
    sourceSilentChangesExact composition framed refl refl delta-result
      (sourceStepChangesExact delta-world′)

  combined-result =
    sourceSilentResultExact composition framed refl refl delta-result
      (sourceStepResultExact delta-world′)

  combined-world =
    sourceSilentWorldCoherent composition framed refl refl delta-result
      (sourceStepWorldCoherent delta-world′)

  combined-exclusive =
    sourceSilentSourceNameExclusive
      composition framed refl refl delta-result
      (sourceStepSourceNameExclusive delta-world′)

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition framed refl refl delta-result
      (sourceStepAssumptionMembershipUnique delta-world′)


finish-left-then-right-deltaᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceDeltaRootᵀ →
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {m n : ℕ} {L′ R′ : Term} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK L′ →
  No• R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ $ (κℕ m) ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ $ (κℕ n) ⊑ R′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {M′ = L′ ⊕[ addℕ ] R′}
    {L = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ⁺} idι
finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf runtime-left no-right
    left-relation right-relation
    with right-catchup
      prefix coherent exclusive unique target-wf runtime-left
      ($ (κℕ _)) no•-$ left-relation
finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf runtime-left no-right
    left-relation right-relation
    | left-world
    with related-nat-source-constant-target-valueᵀ
      (rightCatchupTargetValue left-catchup)
      (right-catchup-final-nat-relationᵀ left-catchup)
  where
  left-catchup = worldRightCatchupResult left-world
finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf runtime-left no-right
    left-relation right-relation
    | left-world | target-left≡
    with rightCatchupSourceChangesEmpty
           (worldRightCatchupResult left-world)
       | rightCatchupSourceUnchanged
           (worldRightCatchupResult left-world)
       | target-left≡
finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf runtime-left no-right
    left-relation right-relation
    | left-world | target-left≡ | refl | refl | refl =
  world-coherent-source-one-step-indexed
    combined-indexed
    combined-lineage
    combined-changes
    combined-result
    combined-world
    combined-exclusive
    combined-unique
  where
  left-catchup = worldRightCatchupResult left-world
  left-indexed = rightCatchupIndexedResult left-catchup
  left-result = weakIndexedResult left-indexed
  left-transport = weakIndexedTransport (rightCatchupIndexedResult left-catchup)

  source-right-typing⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      no•-$ (nu-term-imprecision-source-typing right-relation)

  target-right-typing⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      no-right (nu-term-imprecision-target-typing right-relation)

  right-relation⁺ =
    allocation-prefixᵀ prefix right-relation
      source-right-typing⁺ target-right-typing⁺

  framed-left =
    delta-⊕₁-frameᵀ
      no•-$ no-right right-relation⁺ left-indexed left-transport

  framed-left-transport =
    weak-step-transport (transportNo•Terms left-transport)

  framed-left-coherence =
    weak-step-type-coherence
      (transportArrowCoherent
        (weakIndexedTypeCoherence (rightCatchupIndexedResult left-catchup)))
      (transportAllCoherent
        (weakIndexedTypeCoherence (rightCatchupIndexedResult left-catchup)))

  framed-left-lineage =
    delta-⊕₁-frame-lineageᵀ
      no•-$ no-right right-relation⁺ left-indexed left-transport
      (worldRightCatchupStoreLineage left-world)

  right-final-relation =
    transport-term-to-ℕᵀ
      (applyTys-ℕ (sourceChanges left-result))
      (target-ℕ-result keep (targetTailChanges left-result))
      (transportNo•Terms
        left-transport no•-$ no-right right-relation⁺)

  right-world =
    right-catchup
      prefix-reflⁱ
      (worldRightCatchupCoherence left-world)
      (worldRightCatchupSourceNameExclusive left-world)
      (worldRightCatchupAssumptionMembershipUnique left-world)
      (worldRightCatchupTargetStoreWf left-world)
      (ok-no
        (applyTerms-preserves-No•
          (targetTailChanges left-result) no-right))
      ($ (κℕ _)) no•-$ right-final-relation

  phase-two =
    finish-right-catchup-deltaᵀ composition delta right-world

  phase-two-indexed = sourceStepIndexedResult phase-two
  phase-two-result = weakIndexedResult phase-two-indexed

  combined =
    sourceSilentResult
      composition framed-left refl refl phase-two-result

  combined-transport =
    sourceSilentTransport
      composition framed-left refl refl phase-two-result
      framed-left-transport (weakIndexedTransport (sourceStepIndexedResult phase-two))

  combined-coherence =
    sourceSilentTypeCoherence
      composition framed-left refl refl phase-two-result
      framed-left-coherence (weakIndexedTypeCoherence (sourceStepIndexedResult phase-two))

  combined-indexed : WeakOneStepIndexedResult idι
  combined-indexed =
    weak-one-step-index-resultᵀ combined
      (nat-result-type-unique combined)
      combined-transport combined-coherence

  combined-lineage =
    sourceSilentStoreLineage
      composition framed-left refl refl phase-two-result
      framed-left-lineage (sourceStepStoreLineage phase-two)

  combined-changes =
    sourceSilentChangesExact
      composition framed-left refl refl phase-two-result
      (sourceStepChangesExact phase-two)

  combined-result =
    sourceSilentResultExact
      composition framed-left refl refl phase-two-result
      (sourceStepResultExact phase-two)

  combined-world =
    sourceSilentWorldCoherent
      composition framed-left refl refl phase-two-result
      (sourceStepWorldCoherent phase-two)

  combined-exclusive =
    sourceSilentSourceNameExclusive
      composition framed-left refl refl phase-two-result
      (sourceStepSourceNameExclusive phase-two)

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition framed-left refl refl phase-two-result
      (sourceStepAssumptionMembershipUnique phase-two)


world-coherent-source-primitive-delta-direct-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceDeltaRootᵀ →
  WorldCoherentSourcePrimitiveDeltaDirectᵀ
world-coherent-source-primitive-delta-direct-proofᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    (ok-no (no•-⊕ no-left no-right))
    left-relation right-relation =
  finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    (ok-no no-left) no-right left-relation right-relation
world-coherent-source-primitive-delta-direct-proofᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    (ok-⊕₁ runtime-left no-right)
    left-relation right-relation =
  finish-left-then-right-deltaᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    runtime-left no-right left-relation right-relation
world-coherent-source-primitive-delta-direct-proofᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    (ok-⊕₂ value-left no-left runtime-right)
    left-relation right-relation
    with related-nat-source-constant-target-valueᵀ
      value-left left-relation
world-coherent-source-primitive-delta-direct-proofᵀ
    right-catchup composition delta
    prefix coherent exclusive unique target-wf
    (ok-⊕₂ value-left no-left runtime-right)
    left-relation right-relation | refl =
  finish-right-catchup-deltaᵀ composition delta
    (right-catchup
      prefix coherent exclusive unique target-wf runtime-right
      ($ (κℕ _)) no•-$ right-relation)
