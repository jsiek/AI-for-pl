module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedCastFrameProof
  where

-- File Charter:
--   * Proves target `ξ-⟨⟩` framing under the exact `conv⊑convᵀ` paired-cast
--     constructor.
--   * Transports PairedCast through the actual leading target store change
--     and the complete store lineage of the inner weak result.
--   * Preserves all ten indexed transport/coherence operations and the exact
--     WeakOneStepStoreLineage.
--   * Contains no active cast root, quotient case, recursive dispatcher,
--     postulate, hole, permissive option, or theorem-fragment alias.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; applyTy
  ; applyTys
  ; _—→[_]_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; conv⊑convᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; canonicalIndexedResults
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
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTypeResult
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
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)
open import proof.Right.Core.NuImprecisionPairedCastTransportLemma
  using (paired-cast-transportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )


private
  paired-cast-frame-result :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M N′ : Term} {A A′ B B′ : Ty}
      {c c′ : Coercion} {χ : StoreChange}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    (inner : WeakOneStepResult ρ M N′ A A′ χ) →
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⟨
            applyCoercions (sourceChanges inner) c ⟩
        ⊑ targetResult inner ⟨
            applyCoercions (targetTailChanges inner)
              (applyCoercion χ c′) ⟩
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
    WeakOneStepResult ρ
      (M ⟨ c ⟩) (N′ ⟨ applyCoercion χ c′ ⟩)
      B B′ χ
  paired-cast-frame-result
      {c = c} {c′ = c′} {χ = χ} inner final =
    weak-step-result
      (sourceChanges inner)
      (targetTailChanges inner)
      (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) c ⟩)
      (targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ c′) ⟩)
      (resultCtx inner)
      (resultLeftCtx inner)
      (resultRightCtx inner)
      (sourceCtxResult inner)
      (targetCtxResult inner)
      (resultStore inner)
      (applyTys (sourceChanges inner) _)
      (applyTys (targetTailChanges inner) (applyTy χ _))
      refl
      refl
      (transportType inner)
      (transportAllBody inner)
      (transportRightBody inner)
      (transportSourceNu inner)
      (transportType inner _)
      (cast-↠ (sourceCatchup inner))
      (cast-↠ (targetTail inner))
      (sourceStoreResult inner)
      (targetStoreResult inner)
      final


world-coherent-right-one-step-paired-cast-frame-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ N′ : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  M′ —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {A = A} {B = A′}
    {χ = χ} {ρ = ρ} p →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩}
    {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} q
world-coherent-right-one-step-paired-cast-frame-proofᵀ
    paired _
    (world-indexed-outcome-related
      indexed lineage coherent exclusive unique) =
  world-indexed-outcome-related
    framed-indexed
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique
  where
  inner = weakIndexedResult indexed

  final-paired =
    paired-cast-transportᵀ
      prefix-reflⁱ inner
      (weakIndexedTypeCoherence indexed)
      lineage coherent paired

  final-relation =
    conv⊑convᵀ final-paired (canonicalIndexedResults indexed)

  framed =
    paired-cast-frame-result inner final-relation

  framed-indexed =
    weak-indexed-result framed (relatedResults framed)
      (weak-step-transport
        (transportNo•Terms (weakIndexedTransport indexed)))
      (weak-step-type-coherence
        (transportArrowCoherent (weakIndexedTypeCoherence indexed))
        (transportAllCoherent (weakIndexedTypeCoherence indexed))
        (transportShapeCoherent (weakIndexedTypeCoherence indexed))
        (transportRightBodyShapeCoherent
          (weakIndexedTypeCoherence indexed))
        (transportLeftReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportRightReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportPairedReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportAllBodyPairedReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportSourceNuBodyLeftReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportRightBodyRightReplacementCoherent
          (weakIndexedTypeCoherence indexed)))
world-coherent-right-one-step-paired-cast-frame-proofᵀ
    paired target-step
    (world-indexed-outcome-source-blame source↠) =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ source↠)
