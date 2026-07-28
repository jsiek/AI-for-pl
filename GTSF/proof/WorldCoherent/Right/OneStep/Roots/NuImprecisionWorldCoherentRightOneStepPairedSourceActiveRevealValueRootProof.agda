module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveRevealValueRootProof
  where

-- File Charter:
--   * Proves the arbitrary-inner source-active value root for the exact live
--     paired-reveal constructor.
--   * Transports constructor evidence through completed lineage, frames the
--     final relation neutrally, and invokes matching final synchronization.
--   * Contains no conceal or widening case, retired `PairedCast` abstraction,
--     quotient case, recursive
--     dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (keep; _—→_)
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
  ( paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import
  proof.Catchup.Core.NuImprecisionCatchupPairedFrameProof
  using (weak-one-step-paired-frameᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
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
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions-reflects-Inert)
open import
  proof.Right.Core.NuImprecisionPairedConversionTransportProof
  using
  ( paired-conceal-evidence-transportᵀ
  ; paired-reveal-evidence-transportᵀ
  )
open import
  proof.Right.Core.NuImprecisionPairedWideningTransportProof
  using (paired-widening-evidence-transportᵀ)
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using (WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ)
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


active-paired-reveal-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
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
  (Inert c → ⊥) →
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
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
    M⊑V′ target-root
    with catchup coherent exclusive unique wfL
      (runtime-⟨⟩ ok-source) vV′
      (runtime-value-no• (runtime-⟨⟩ ok-target) vV′) M⊑V′
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ
      (sourceCatchup
        (weakIndexedResult (catchupIndexedResult caught))))
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
    M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW) | refl | refl
    with paired-reveal-evidence-transportᵀ
      prefix-reflⁱ
      (weakIndexedResult (catchupIndexedResult caught))
      (silentInvariant (catchupIndexedInvariant caught))
      (weakIndexedTypeCoherence (catchupIndexedResult caught))
      lineage
      corr c↑ c′↑ replacement
active-paired-reveal-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert corr c↑ c′↑ replacement
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
  final-inner = canonicalIndexedResults indexed
  final-relation =
    paired-revealᵀ corr′ cˢ↑ cᵗ↑ replacement′ final-inner
  framed = weak-one-step-paired-frameᵀ inner final-relation
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
  final-noninert =
    λ final-inert →
      noninert
        (applyCoercions-reflects-Inert
          (sourceChanges inner) _ final-inert)
  final-wfR = final-right-store-wf inner refl wfR
  noV′ = runtime-value-no• (runtime-⟨⟩ ok-target) vV′
  final-outcome =
    synchronize-paired-reveal synchronize
      final-coherent final-exclusive final-unique final-wfL final-wfR
      (ok-no (no•-⟨⟩ noW)) ok-target
      vW noW vV′ noV′ final-noninert
      corr′ cˢ↑ cᵗ↑ replacement′ final-inner target-root
