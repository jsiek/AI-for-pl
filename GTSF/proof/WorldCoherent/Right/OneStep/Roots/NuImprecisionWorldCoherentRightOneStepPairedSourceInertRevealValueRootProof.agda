module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertRevealValueRootProof
  where

-- File Charter:
--   * Proves the exact paired-reveal outer-cast value root when the source
--     cast is inert.
--   * Catches the source inner term to a bullet-free value, transports the
--     exact reveal evidence through lineage, and applies the generic source
--     indexed value root before composing the silent prefix.
--   * Does not treat the target-inert bridge branch as source-inert evidence.
--   * Contains no conceal or widening case, active-source synchronization,
--     retired `PairedCast` abstraction, quotient case, recursive dispatcher,
--     postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; pure-step; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( paired-revealᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; TyVar)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; silentInvariant
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; sourceResult
  ; targetCtxResult
  ; targetIsUnchanged
  ; targetStoreResult
  ; targetTailChanges
  ; targetTailIsEmpty
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportLeftReplacementCoherent
  ; transportNo•Terms
  ; transportPairedReplacementCoherent
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; WeakOneStepResult
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions-preserves-Inert)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Right.Core.NuImprecisionPairedConversionTransportProof
  using (paired-reveal-evidence-transportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootDef
  using (WorldCoherentRightOneStepValueIndexedRootᵀ)
open import
  proof.Catchup.Core.NuImprecisionCatchupPairedFrameProof
  using (weak-one-step-paired-frameᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  final-right-store-wf :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ : Ty}
      (inner : WeakOneStepResult ρ M V′ A A′ keep) →
    targetTailChanges inner ≡ [] →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    StoreWf (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
  final-right-store-wf {ρ = ρ} inner refl wfR =
    subst (StoreWf (resultRightCtx inner))
      (sym (targetStoreResult inner))
      (subst (λ Δ → StoreWf Δ (rightStoreⁱ ρ))
        (sym (targetCtxResult inner)) wfR)


inert-paired-reveal-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepValueIndexedRootᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ N′ : Term} {A A′ B B′ X X′ : Ty}
    {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (M ⟨ c ⟩) →
  RuntimeOK (V′ ⟨ c′ ⟩) →
  Value V′ →
  Inert c →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  V′ ⟨ c′ ⟩ —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′}
    {χ = keep} {ρ = ρ} q
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    with catchup coherent exclusive unique wfL
      (runtime-⟨⟩ ok-source) vV′
      (runtime-value-no• (runtime-⟨⟩ ok-target) vV′) M⊑V′
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ
      (sourceCatchup
        (weakIndexedResult (catchupIndexedResult caught))))
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW) | refl | refl
    with paired-reveal-evidence-transportᵀ
      prefix-reflⁱ
      (weakIndexedResult (catchupIndexedResult caught))
      (silentInvariant (catchupIndexedInvariant caught))
      (weakIndexedTypeCoherence (catchupIndexedResult caught))
      lineage corr c↑ c′↑ replacement
inert-paired-reveal-root-proofᵀ
    catchup value-root coherent exclusive unique wfL wfR
    ok-source ok-target vV′ inert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW) | refl | refl
    | pX′ , μˢ , μᵗ , corr′ , cˢ↑ , cᵗ↑ , replacement′ =
  world-coherent-left-silent-then-outcomeᵀ
    framed-silent framed-lineage final-outcome
  where
  indexed = catchupIndexedResult caught
  inner = weakIndexedResult indexed

  final-relation =
    paired-revealᵀ
      corr′ cˢ↑ cᵗ↑ replacement′
      (canonicalIndexedResults indexed)

  framed =
    weak-one-step-paired-frameᵀ inner final-relation

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

  framed-silent =
    left-silent-indexed framed-indexed
      (left-silent-invariant refl refl)
      (ok-no (no•-⟨⟩ noW))

  framed-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  final-inert =
    applyCoercions-preserves-Inert (sourceChanges inner) inert

  final-wfR =
    final-right-store-wf inner refl wfR

  final-outcome =
    value-root {χ = keep} prefix-reflⁱ
      final-coherent final-exclusive final-unique final-wfR
      ok-target (vW ⟨ final-inert ⟩) (no•-⟨⟩ noW)
      final-relation (pure-step target-root)
