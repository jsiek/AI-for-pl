module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepBinaryFramesProof
  where

-- File Charter:
--   * Implements exact world-coherent source one-step binary frames.
--   * Reuses exported weak application frames and locally reproduces the
--     private primitive indexed-frame record construction.
--   * Preserves source-step exact changes, exact source result, transport,
--     type coherence, store lineage, world coherence, and exclusivity.
--   * Contains no dispatcher, outcome carrier, postulate, hole, or permissive
--     option.

open import Data.List using ([]; _∷_)
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _·_
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_; ⊕⊑⊕ᵀ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  ; ‵_
  ; `ℕ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-indexed-arrow-resultᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-·₁-frame-preserves-transportᵀ
  ; weak-one-step-·₁-frame-preserves-type-coherenceᵀ
  ; weak-one-step-·₁-frameᵀ
  ; weak-one-step-·₂-indexed-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalArrowResults
  ; canonicalIndexedResults
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportAllBody
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; transportRightBody
  ; transportSourceNu
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakArrowResult
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepBinaryFramesDef
  using
  ( WorldCoherentSourceOneStepBinaryFrames
  ; sourceStepApplicationLeftFrame
  ; sourceStepApplicationRightFrame
  ; sourceStepPrimitiveLeftFrame
  ; sourceStepPrimitiveRightFrame
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTys-ℕ
  ; applyTy-ℕ
  ; ⊕₁-↠
  ; ⊕₂-↠
  )


private
  target-ℕ-result :
    ∀ (χ : StoreChange) (χs : StoreChanges) →
    applyTys χs (applyTy χ (‵ `ℕ)) ≡ ‵ `ℕ
  target-ℕ-result χ χs =
    trans (cong (applyTys χs) (applyTy-ℕ χ)) (applyTys-ℕ χs)

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

  transport-term-to-ℕᵀ :
    ∀ {Φ Δᴸ Δᴿ A B ρ γ M M′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (A≡ℕ : A ≡ ‵ `ℕ) →
    (B≡ℕ : B ≡ ‵ `ℕ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
  transport-term-to-ℕᵀ {p = p} A≡ℕ B≡ℕ M⊑M′ =
    nu-term-imprecision-transport-typesᵀ
      A≡ℕ B≡ℕ (transport-idι-to-ℕ A≡ℕ B≡ℕ p) M⊑M′

  weak-one-step-⊕₁-indexed-frameᵀ :
    ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    (inner : WeakOneStepIndexedResult
      {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι) →
    WeakOneStepTransport (weakIndexedResult inner) →
    WeakOneStepTypeCoherence (weakIndexedResult inner) →
    WeakOneStepIndexedResult
      {M = L ⊕[ addℕ ] M}
      {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
      {χ = χ} {ρ = ρ} idι
  weak-one-step-⊕₁-indexed-frameᵀ
      {L = L} {L₁′ = L₁′} {M = M} {M′ = M′}
      {χ = χ} {ρ = ρ} noM noM′ M⊑M′ inner transport coherence =
    weak-one-step-index-resultᵀ framed
      (transport-idι-from-ℕ
        source-ℕ target-ℕ (transportType base idι))
      framed-transport framed-coherence
    where
    base = weakIndexedResult inner

    source-ℕ = applyTys-ℕ (sourceChanges base)
    target-ℕ = target-ℕ-result χ (targetTailChanges base)

    left-related =
      transport-term-to-ℕᵀ
        source-ℕ target-ℕ (canonicalIndexedResults inner)

    right-related =
      transport-term-to-ℕᵀ source-ℕ target-ℕ
        (transportNo•Terms transport noM noM′ M⊑M′)
    framed-transport = weak-step-transport (transportNo•Terms transport)
    framed-coherence =
      weak-step-type-coherence
        (transportArrowCoherent coherence)
        (transportAllCoherent coherence)

    framed :
      WeakOneStepResult ρ
        (L ⊕[ addℕ ] M)
        (L₁′ ⊕[ addℕ ] applyTerm χ M′)
        (‵ `ℕ) (‵ `ℕ) χ
    framed =
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
        ; transportSourceNu = transportSourceNu base
        ; resultType = idι
        ; sourceCatchup = ⊕₁-↠ noM (sourceCatchup base)
        ; targetTail =
            ⊕₁-↠ (applyTerm-preserves-No• χ noM′)
              (targetTail base)
        ; sourceStoreResult = sourceStoreResult base
        ; targetStoreResult = targetStoreResult base
        ; relatedResults = ⊕⊑⊕ᵀ left-related right-related
        }

  weak-one-step-⊕₂-indexed-frameᵀ :
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
    WeakOneStepTypeCoherence (weakIndexedResult inner) →
    WeakOneStepIndexedResult
      {M = L ⊕[ addℕ ] M}
      {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
      {χ = χ} {ρ = ρ} idι
  weak-one-step-⊕₂-indexed-frameᵀ
      {L = L} {L′ = L′} {M = M} {M₁′ = M₁′}
      {χ = χ} {ρ = ρ} vL noL vL′ noL′ L⊑L′ inner transport
      coherence =
    weak-one-step-index-resultᵀ framed
      (transport-idι-from-ℕ
        source-ℕ target-ℕ (transportType base idι))
      framed-transport framed-coherence
    where
    base = weakIndexedResult inner

    source-ℕ = applyTys-ℕ (sourceChanges base)
    target-ℕ = target-ℕ-result χ (targetTailChanges base)

    left-related =
      transport-term-to-ℕᵀ source-ℕ target-ℕ
        (transportNo•Terms transport noL noL′ L⊑L′)

    right-related =
      transport-term-to-ℕᵀ
        source-ℕ target-ℕ (canonicalIndexedResults inner)
    framed-transport = weak-step-transport (transportNo•Terms transport)
    framed-coherence =
      weak-step-type-coherence
        (transportArrowCoherent coherence)
        (transportAllCoherent coherence)

    framed :
      WeakOneStepResult ρ
        (L ⊕[ addℕ ] M)
        (applyTerm χ L′ ⊕[ addℕ ] M₁′)
        (‵ `ℕ) (‵ `ℕ) χ
    framed =
      record
        { sourceChanges = sourceChanges base
        ; targetTailChanges = targetTailChanges base
        ; sourceResult =
            applyTerms (sourceChanges base) L ⊕[ addℕ ]
              sourceResult base
        ; targetResult =
            (applyTerms (targetTailChanges base) (applyTerm χ L′))
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
        ; transportSourceNu = transportSourceNu base
        ; resultType = idι
        ; sourceCatchup = ⊕₂-↠ vL noL (sourceCatchup base)
        ; targetTail =
            ⊕₂-↠
              (applyTerm-preserves-Value χ vL′)
              (applyTerm-preserves-No• χ noL′)
              (targetTail base)
        ; sourceStoreResult = sourceStoreResult base
        ; targetStoreResult = targetStoreResult base
        ; relatedResults = ⊕⊑⊕ᵀ left-related right-related
        }


source-step-application-left-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ L₁ M M′ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentSourceOneStepIndexedResult
    {M = L} {M′ = L′} {L = L₁}
    {A = A ⇒ B} {B = A′ ⇒ B′}
    {χ = χ} {ρ = ρ} (pA ↦ pB) →
  WorldCoherentSourceOneStepIndexedResult
    {M = L · M} {M′ = L′ · M′}
    {L = L₁ · applyTerm χ M}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
source-step-application-left-frameᵀ
    {M = M} {χ = χ} noM noM′ M⊑M′ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀
  arrow =
    weak-indexed-arrow-resultᵀ indexed₀
  L⊑L′ = canonicalArrowResults arrow
  transported-M =
    transportNo•Terms
      (weakIndexedTransport (sourceStepIndexedResult complete)) noM noM′ M⊑M′

  framed =
    weak-one-step-·₁-frameᵀ noM noM′ inner L⊑L′ transported-M
  framed-transport =
    weak-one-step-·₁-frame-preserves-transportᵀ
      noM noM′ inner L⊑L′ transported-M
      (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-·₁-frame-preserves-type-coherenceᵀ
      noM noM′ inner L⊑L′ transported-M
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete))
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence

  term-exact :
    applyTerms (sourceChanges inner) M ≡ applyTerm χ M
  term-exact =
    cong (λ χs → applyTerms χs M) (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _·_ (sourceStepResultExact complete) term-exact


source-step-application-right-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ M M′ M₁ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = M₁}
    {A = A} {B = A′} {χ = χ} {ρ = ρ} pA →
  WorldCoherentSourceOneStepIndexedResult
    {M = V · M} {M′ = V′ · M′}
    {L = applyTerm χ V · M₁}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
source-step-application-right-frameᵀ
    {V = V} {χ = χ} vV noV vV′ noV′ V⊑V′ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀
  framed-indexed =
    weak-one-step-·₂-indexed-frameᵀ
      vV noV vV′ noV′ V⊑V′ indexed₀
      (weakIndexedTransport (sourceStepIndexedResult complete))
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  term-exact :
    applyTerms (sourceChanges inner) V ≡ applyTerm χ V
  term-exact =
    cong (λ χs → applyTerms χs V) (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _·_ term-exact (sourceStepResultExact complete)


source-step-primitive-left-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ L₁ M M′ : Term} {χ : StoreChange} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = L} {M′ = L′} {L = L₁}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = χ} {ρ = ρ} idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = L ⊕[ addℕ ] M}
    {M′ = L′ ⊕[ addℕ ] M′}
    {L = L₁ ⊕[ addℕ ] applyTerm χ M}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = χ} {ρ = ρ} idι
source-step-primitive-left-frameᵀ
    {M = M} {χ = χ} noM noM′ M⊑M′ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀
  framed-indexed =
    weak-one-step-⊕₁-indexed-frameᵀ
      noM noM′ M⊑M′ indexed₀
      (weakIndexedTransport (sourceStepIndexedResult complete))
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  term-exact :
    applyTerms (sourceChanges inner) M ≡ applyTerm χ M
  term-exact =
    cong (λ χs → applyTerms χs M) (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂
      (λ L₀ M₀ → L₀ ⊕[ addℕ ] M₀)
      (sourceStepResultExact complete)
      term-exact


source-step-primitive-right-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ M M′ M₁ : Term} {χ : StoreChange} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = M₁}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = χ} {ρ = ρ} idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = V ⊕[ addℕ ] M}
    {M′ = V′ ⊕[ addℕ ] M′}
    {L = applyTerm χ V ⊕[ addℕ ] M₁}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = χ} {ρ = ρ} idι
source-step-primitive-right-frameᵀ
    {V = V} {χ = χ} vV noV vV′ noV′ V⊑V′ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀
  framed-indexed =
    weak-one-step-⊕₂-indexed-frameᵀ
      vV noV vV′ noV′ V⊑V′ indexed₀
      (weakIndexedTransport (sourceStepIndexedResult complete))
      (weakIndexedTypeCoherence (sourceStepIndexedResult complete))

  term-exact :
    applyTerms (sourceChanges inner) V ≡ applyTerm χ V
  term-exact =
    cong (λ χs → applyTerms χs V) (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂
      (λ L₀ M₀ → L₀ ⊕[ addℕ ] M₀)
      term-exact
      (sourceStepResultExact complete)


world-coherent-source-one-step-binary-frames-proofᵀ :
  WorldCoherentSourceOneStepBinaryFrames
world-coherent-source-one-step-binary-frames-proofᵀ = record
  { sourceStepApplicationLeftFrame = source-step-application-left-frameᵀ
  ; sourceStepApplicationRightFrame = source-step-application-right-frameᵀ
  ; sourceStepPrimitiveLeftFrame = source-step-primitive-left-frameᵀ
  ; sourceStepPrimitiveRightFrame = source-step-primitive-right-frameᵀ
  }
