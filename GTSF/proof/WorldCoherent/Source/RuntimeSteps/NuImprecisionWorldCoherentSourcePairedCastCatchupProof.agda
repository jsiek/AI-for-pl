module proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePairedCastCatchupProof where

-- File Charter:
--   * Composes accumulated-world paired-cast transport with exact-world
--     terminal paired-cast catch-up.
--   * Frames both casts without changing the final world, contexts, or
--     source/target change lists.
--   * Carries an independent runtime sibling through a full exact-final
--     caught-result/sibling continuation.
--   * Contains no StoreCorresponds transport or terminal cast semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; Inert)
open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyCoercion
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; StoreImpPrefix
  ; conv⊑convᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.Left.SilentTransport.NuImprecisionLeftSilentPairedCastTransportDef using
  (LeftSilentPairedCastTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCatchup
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
  ; transportPairedReplacementCoherent
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportNo•Terms
  ; transportRightBody
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
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
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastCatchupDef using
  (WorldCoherentFinalPairedCastCatchupᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupDef
  using (WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePairedCastCatchupDef using
  (WorldCoherentSourcePairedCastCatchupᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-RuntimeOK
  ; cast-↠
  )


weak-one-step-paired-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A A′ B B′ c c′}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M M′ A A′ keep) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) c ⟩)
      ⊑ (targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′) ⟩)
    ⦂ applyTys (sourceChanges inner) B ⊑
      applyTys (targetTailChanges inner) (applyTy keep B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ
    (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) B B′ keep
weak-one-step-paired-cast-frameᵀ
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    inner final =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner ⟨
        applyCoercions (sourceChanges inner) c ⟩
    ; targetResult = targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′) ⟩
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy keep B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (sourceCatchup inner)
    ; targetTail = cast-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = final
    }


terminal-runtime :
  ∀ {W : Term} →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  RuntimeOK W
terminal-runtime (inj₁ (vW , noW)) = ok-no noW
terminal-runtime (inj₂ refl) = ok-no no•-blame


world-coherent-source-paired-cast-catchup-proofᵀ :
  LeftSilentPairedCastTransportᵀ →
  WorldCoherentFinalPairedCastCatchupᵀ →
  WorldCoherentSourcePairedCastCatchupᵀ
world-coherent-source-paired-cast-catchup-proofᵀ
    transport-paired final-catchup prefix paired
    vV′ noV′ inert-c′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent first-lineage second
  where
  inner = weakIndexedResult indexed

  final-paired =
    transport-paired prefix inner silent
      (weakIndexedTypeCoherence indexed) lineage coherent paired

  final-relation =
    conv⊑convᵀ final-paired (canonicalIndexedResults indexed)

  first = weak-one-step-paired-cast-frameᵀ inner final-relation

  first-lineage = weak-step-store-lineage
    (lineageStore lineage)
    (lineageEmbedding lineage)
    (lineagePrefix lineage)

  first-indexed = weak-indexed-result first (relatedResults first)
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

  first-silent =
    left-silent-indexed
      first-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (terminal-runtime final))

  second =
    final-catchup coherent exclusive unique wfL final
      vV′ noV′ inert-c′ final-paired
      (canonicalIndexedResults indexed)


world-coherent-source-paired-cast-runtime-sibling-catchup-proofᵀ :
  LeftSilentPairedCastTransportᵀ →
  WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A A′ B B′ E E′ : Ty}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  PairedCast Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  Value V′ →
  No• V′ →
  Inert c′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
  (let result =
         weakIndexedResult
           (catchupIndexedResult (worldCatchupResult inner))
   in
   resultCtx result
     ∣ resultLeftCtx result
     ∣ resultRightCtx result
     ∣ resultStore result ∣ []
     ⊢ᴺ applyTerms (sourceChanges result) R
       ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
     ⦂ applyTys (sourceChanges result) E
       ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
     ∶ transportType result r) →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ c ⟩} {V′ = V′ ⟨ c′ ⟩} {ρ = ρ⁺} q ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
      ∶ transportType result r
world-coherent-source-paired-cast-runtime-sibling-catchup-proofᵀ
    transport-paired final-catchup
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix paired vV′ noV′ inert-c′ noR okR′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL)
    inner-sibling =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage second
  where
  inner = weakIndexedResult indexed

  final-paired =
    transport-paired prefix inner silent
      (weakIndexedTypeCoherence indexed) lineage coherent paired

  final-relation =
    conv⊑convᵀ final-paired (canonicalIndexedResults indexed)

  first = weak-one-step-paired-cast-frameᵀ inner final-relation

  first-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  first-indexed =
    weak-indexed-result first (relatedResults first)
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

  first-silent =
    left-silent-indexed
      first-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (terminal-runtime final))

  second =
    final-catchup
      coherent exclusive unique wfL final
      vV′ noV′ inert-c′ final-paired
      (canonicalIndexedResults indexed)
      (applyTerms-preserves-No• (sourceChanges inner) noR)
      (applyTerms-preserves-RuntimeOK
        (targetTailChanges inner) okR′)
      inner-sibling
