module proof.OneStep.NuImprecisionOneStepPrimitiveFrames where

-- File Charter:
--   * Owns normalized natural-number index transport for primitive frames.
--   * Frames already-computed indexed results and outcomes, including a
--     left-silent prefix with a relation transported in lockstep.
--   * Covers only addition evaluation contexts; primitive delta, scheduling
--     boundaries, and root blame live elsewhere.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Data.List using ([]; _∷_; _++_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_; idι)
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; _—↠[_]_
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; blame-⊕₁
  ; blame-⊕₂
  ; keep
  ; pure-step
  ; ↠-refl
  ; ↠-step
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (No•; Value; blame; _⊕[_]_)
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_; ⊕⊑⊕ᵀ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)
open import Types using (`ℕ; ‵_)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-one-step-index-resultᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepIndexedOutcome
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; left-silent-invariant
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
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportLeftReplacementCoherent
  ; transportNo•Terms
  ; transportPairedReplacementCoherent
  ; transportRightBody
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTerms-preserves-Value
  ; applyTys-ℕ
  ; applyTy-ℕ
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; ↠-trans
  )


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


weak-one-step-left-silent-⊕₁-transported-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  (inner : WeakOneStepIndexedResult
    {M = L} {N′ = L′}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ} idι) →
  LeftSilentInvariant (weakIndexedResult inner) →
  let base = weakIndexedResult inner in
  resultCtx base
    ∣ resultLeftCtx base
    ∣ resultRightCtx base
    ∣ resultStore base ∣ []
    ⊢ᴺ applyTerms (sourceChanges base) M
      ⊑ applyTerms (targetTailChanges base) (applyTerm keep M′)
    ⦂ applyTys (sourceChanges base) (‵ `ℕ)
      ⊑ applyTys (targetTailChanges base) (applyTy keep (‵ `ℕ))
    ∶ transportType base idι →
  WeakOneStepIndexedResult
    {M = L ⊕[ addℕ ] M}
    {N′ = L′ ⊕[ addℕ ] M′}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ} idι
weak-one-step-left-silent-⊕₁-transported-frameᵀ
    {L = L} {L′ = L′} {M = M} {M′ = M′} {ρ = ρ}
    noM inner (left-silent-invariant refl refl) M⊑M′ =
  weak-one-step-index-resultᵀ framed
    (transport-idι-from-ℕ
      source-ℕ target-ℕ (transportType base idι))
    framed-transport framed-coherence
  where
  base = weakIndexedResult inner
  source-ℕ = applyTys-ℕ (sourceChanges base)
  target-ℕ = target-ℕ-result keep []

  left-related =
    transport-term-to-ℕᵀ source-ℕ target-ℕ
      (canonicalIndexedResults inner)

  right-related =
    transport-term-to-ℕᵀ source-ℕ target-ℕ M⊑M′

  framed :
    WeakOneStepResult ρ
      (L ⊕[ addℕ ] M)
      (L′ ⊕[ addℕ ] M′)
      (‵ `ℕ) (‵ `ℕ) keep
  framed =
    record
      { sourceChanges = sourceChanges base
      ; targetTailChanges = []
      ; sourceResult =
          sourceResult base ⊕[ addℕ ]
            applyTerms (sourceChanges base) M
      ; targetResult = targetResult base ⊕[ addℕ ] M′
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
      ; targetTail = ↠-refl
      ; sourceStoreResult = sourceStoreResult base
      ; targetStoreResult = targetStoreResult base
      ; relatedResults = ⊕⊑⊕ᵀ left-related right-related
      }

  framed-transport : WeakOneStepTransport framed
  framed-transport =
    weak-step-transport
      (transportNo•Terms (weakIndexedTransport inner))

  framed-coherence : WeakOneStepTypeCoherence framed
  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent
        (weakIndexedTypeCoherence inner))
      (transportAllCoherent
        (weakIndexedTypeCoherence inner))
      (transportShapeCoherent
        (weakIndexedTypeCoherence inner))
      (transportRightBodyShapeCoherent
        (weakIndexedTypeCoherence inner))
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence inner))
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence inner))
      (transportPairedReplacementCoherent
        (weakIndexedTypeCoherence inner))
      (transportAllBodyPairedReplacementCoherent
        (weakIndexedTypeCoherence inner))
      (transportSourceNuBodyLeftReplacementCoherent
        (weakIndexedTypeCoherence inner))
      (transportRightBodyRightReplacementCoherent
        (weakIndexedTypeCoherence inner))


private

  ⊕₁-blame-tail :
    ∀ {L M χs} →
    No• M →
    L —↠[ χs ] blame →
    L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
  ⊕₁-blame-tail noM L↠blame =
    ↠-trans (⊕₁-↠ noM L↠blame)
      (↠-step (pure-step blame-⊕₁) ↠-refl)

  ⊕₂-blame-tail :
    ∀ {L M χs} →
    Value L →
    No• L →
    M —↠[ χs ] blame →
    L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
  ⊕₂-blame-tail {χs = χs} vL noL M↠blame =
    ↠-trans (⊕₂-↠ vL noL M↠blame)
      (↠-step
        (pure-step
          (blame-⊕₂ (applyTerms-preserves-Value χs vL)))
        ↠-refl)

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
      {L = L} {L₁′ = L₁′} {M = M} {M′ = M′} {χ = χ}
      {ρ = ρ} noM noM′ M⊑M′ inner transport coherence =
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
        (transportShapeCoherent coherence)
        (transportRightBodyShapeCoherent coherence)
        (transportLeftReplacementCoherent coherence)
        (transportRightReplacementCoherent coherence)
        (transportPairedReplacementCoherent coherence)
        (transportAllBodyPairedReplacementCoherent coherence)
        (transportSourceNuBodyLeftReplacementCoherent coherence)
        (transportRightBodyRightReplacementCoherent coherence)

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
      {L = L} {L′ = L′} {M = M} {M₁′ = M₁′} {χ = χ}
      {ρ = ρ} vL noL vL′ noL′ L⊑L′ inner transport coherence =
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
        (transportShapeCoherent coherence)
        (transportRightBodyShapeCoherent coherence)
        (transportLeftReplacementCoherent coherence)
        (transportRightReplacementCoherent coherence)
        (transportPairedReplacementCoherent coherence)
        (transportAllBodyPairedReplacementCoherent coherence)
        (transportSourceNuBodyLeftReplacementCoherent coherence)
        (transportRightBodyRightReplacementCoherent coherence)

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
            applyTerms (targetTailChanges base)
              (applyTerm χ L′) ⊕[ addℕ ] targetResult base
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


weak-one-step-⊕₁-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′
    (indexed-outcome-related inner) =
  indexed-outcome-related
    (weak-one-step-⊕₁-indexed-frameᵀ
      noM noM′ M⊑M′ inner
      (weakIndexedTransport inner)
      (weakIndexedTypeCoherence inner))
weak-one-step-⊕₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (⊕₁-blame-tail noM source↠)


weak-one-step-⊕₂-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′
    (indexed-outcome-related inner) =
  indexed-outcome-related
    (weak-one-step-⊕₂-indexed-frameᵀ
      vL noL vL′ noL′ L⊑L′ inner
      (weakIndexedTransport inner)
      (weakIndexedTypeCoherence inner))
weak-one-step-⊕₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (⊕₂-blame-tail vL noL source↠)


weak-one-step-⊕₁-indexed-frame-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedResult
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedResult
    {M = L ⊕[ addℕ ] M}
    {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₁-indexed-frame-relatedᵀ
    noM noM′ M⊑M′ inner =
  weak-one-step-⊕₁-indexed-frameᵀ
    noM noM′ M⊑M′ inner
    (weakIndexedTransport inner)
    (weakIndexedTypeCoherence inner)


weak-one-step-⊕₂-indexed-frame-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedResult
    {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedResult
    {M = L ⊕[ addℕ ] M}
    {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₂-indexed-frame-relatedᵀ
    vL noL vL′ noL′ L⊑L′ inner =
  weak-one-step-⊕₂-indexed-frameᵀ
    vL noL vL′ noL′ L⊑L′ inner
    (weakIndexedTransport inner)
    (weakIndexedTypeCoherence inner)


weak-one-step-⊕₁-source-blame-frameᵀ :
  ∀ {L M χs} →
  No• M →
  L —↠[ χs ] blame →
  L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
weak-one-step-⊕₁-source-blame-frameᵀ = ⊕₁-blame-tail


weak-one-step-⊕₂-source-blame-frameᵀ :
  ∀ {L M χs} →
  Value L →
  No• L →
  M —↠[ χs ] blame →
  L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
weak-one-step-⊕₂-source-blame-frameᵀ = ⊕₂-blame-tail
