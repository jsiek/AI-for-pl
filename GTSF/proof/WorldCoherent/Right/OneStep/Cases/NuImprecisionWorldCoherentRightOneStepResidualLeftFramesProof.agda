module
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepResidualLeftFramesProof
  where

-- File Charter:
--   * Frames an indexed source-value residual through an application or
--     primitive whose untouched source operand may contain the runtime bullet.
--   * Uses the residual's runtime/no-bullet transport directly and the retained
--     empty source trace to avoid requiring `No•` of the source operand.
--   * Contains no dispatcher, recursive call, postulate, hole, permissive
--     option, compatibility alias, or dependency wrapper.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; ↠-refl
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; _·_
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; ·⊑·ᵀ
  ; ⊕⊑⊕ᵀ
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; `ℕ
  ; ‵_
  ; _⇒_
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-indexed-arrow-resultᵀ
  ; weak-one-step-index-resultᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalArrowResults
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
  ; weakArrowResult
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTerm-preserves-No•
  ; applyTys-ℕ
  ; applyTy-ℕ
  ; ·₁-↠
  ; ⊕₁-↠
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  using
  ( WorldCoherentRightTargetIndexedStepResidualResult
  ; world-coherent-right-target-indexed-step-residual
  )


world-coherent-right-one-step-residual-application-left-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L₁′ M M′ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  RuntimeOK M →
  No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentRightTargetIndexedStepResidualResult
    {ρ = ρ} {V = L} {N′ = L₁′} {χ = χ} (pA ↦ pB) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = L₁′ · applyTerm χ M′}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
world-coherent-right-one-step-residual-application-left-frameᵀ
    {ρ = ρ} {L = L} {L₁′ = L₁′} {M = M} {M′ = M′}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {χ = χ}
    prefix okM noM′ M⊢ M⊑M′
    (world-coherent-right-target-indexed-step-residual
      indexed@(weak-indexed-result inner canonical transport coherence)
      refl refl source-value source-no target-value target-no
      lineage bullet runtime-transport
      final-coherent final-exclusive final-unique final-wfR) =
  world-indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    final-coherent final-exclusive final-unique
  where
  arrow = weak-indexed-arrow-resultᵀ indexed
  left-related = canonicalArrowResults arrow
  right-related =
    runtime-transport prefix okM noM′ M⊢ M⊑M′

  framed :
    WeakOneStepResult ρ
      (L · M) (L₁′ · applyTerm χ M′) B B′ χ
  framed =
    weak-step-result
      []
      (targetTailChanges inner)
      (L · M)
      (targetResult inner ·
        applyTerms (targetTailChanges inner) (applyTerm χ M′))
      (resultCtx inner)
      (resultLeftCtx inner)
      (resultRightCtx inner)
      (sourceCtxResult inner)
      (targetCtxResult inner)
      (resultStore inner)
      _
      _
      refl
      refl
      (transportType inner)
      (transportAllBody inner)
      (transportRightBody inner)
      (transportSourceNu inner)
      (transportType inner _)
      ↠-refl
      (·₁-↠ (applyTerm-preserves-No• χ noM′) (targetTail inner))
      (sourceStoreResult inner)
      (targetStoreResult inner)
      (·⊑·ᵀ left-related right-related)

  framed-transport : WeakOneStepTransport framed
  framed-transport =
    weak-step-transport (transportNo•Terms transport)

  framed-coherence : WeakOneStepTypeCoherence framed
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


private
  target-ℕ-result :
    ∀ χ χs →
    applyTys χs (applyTy χ (‵ `ℕ)) ≡ ‵ `ℕ
  target-ℕ-result χ χs =
    trans (cong (applyTys χs) (applyTy-ℕ χ))
      (applyTys-ℕ χs)

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
    ∀ {Φ Δᴸ Δᴿ A B ρ M M′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (A≡ℕ : A ≡ ‵ `ℕ) →
    (B≡ℕ : B ≡ ‵ `ℕ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
  transport-term-to-ℕᵀ {p = p} A≡ℕ B≡ℕ M⊑M′ =
    nu-term-imprecision-transport-typesᵀ
      A≡ℕ B≡ℕ (transport-idι-to-ℕ A≡ℕ B≡ℕ p) M⊑M′


world-coherent-right-one-step-residual-primitive-left-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L₁′ M M′ : Term} {χ : StoreChange} →
  StoreImpPrefix ρᵇ ρ →
  RuntimeOK M →
  No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ ‵ `ℕ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentRightTargetIndexedStepResidualResult
    {ρ = ρ} {V = L} {N′ = L₁′} {χ = χ} idι →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
    {A = ‵ `ℕ} {B = ‵ `ℕ} {χ = χ} {ρ = ρ} idι
world-coherent-right-one-step-residual-primitive-left-frameᵀ
    {ρ = ρ} {L = L} {L₁′ = L₁′}
    {M = M} {M′ = M′} {χ = χ}
    prefix okM noM′ M⊢ M⊑M′
    (world-coherent-right-target-indexed-step-residual
      indexed@(weak-indexed-result inner canonical transport coherence)
      refl refl source-value source-no target-value target-no
      lineage bullet runtime-transport
      final-coherent final-exclusive final-unique final-wfR) =
  world-indexed-outcome-related
    (weak-one-step-index-resultᵀ framed
      (transport-idι-from-ℕ
        source-ℕ target-ℕ (transportType inner idι))
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    final-coherent final-exclusive final-unique
  where
  source-ℕ = applyTys-ℕ []
  target-ℕ = target-ℕ-result χ (targetTailChanges inner)

  left-related =
    transport-term-to-ℕᵀ source-ℕ target-ℕ canonical
  right-related =
    transport-term-to-ℕᵀ source-ℕ target-ℕ
      (runtime-transport prefix okM noM′ M⊢ M⊑M′)

  framed :
    WeakOneStepResult ρ
      (L ⊕[ addℕ ] M)
      (L₁′ ⊕[ addℕ ] applyTerm χ M′)
      (‵ `ℕ) (‵ `ℕ) χ
  framed =
    weak-step-result
      []
      (targetTailChanges inner)
      (L ⊕[ addℕ ] M)
      (targetResult inner ⊕[ addℕ ]
        applyTerms (targetTailChanges inner) (applyTerm χ M′))
      (resultCtx inner)
      (resultLeftCtx inner)
      (resultRightCtx inner)
      (sourceCtxResult inner)
      (targetCtxResult inner)
      (resultStore inner)
      (‵ `ℕ)
      (‵ `ℕ)
      (sym source-ℕ)
      (sym target-ℕ)
      (transportType inner)
      (transportAllBody inner)
      (transportRightBody inner)
      (transportSourceNu inner)
      idι
      ↠-refl
      (⊕₁-↠ (applyTerm-preserves-No• χ noM′) (targetTail inner))
      (sourceStoreResult inner)
      (targetStoreResult inner)
      (⊕⊑⊕ᵀ left-related right-related)

  framed-transport : WeakOneStepTransport framed
  framed-transport =
    weak-step-transport (transportNo•Terms transport)

  framed-coherence : WeakOneStepTypeCoherence framed
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
