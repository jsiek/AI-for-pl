module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveWideningValueRootProof
  where

-- File Charter:
--   * Proves the arbitrary-inner source-active value root for the exact live
--     paired-widening constructor.
--   * Transports widening evidence through completed lineage, frames the final
--     relation neutrally, and invokes final widening synchronization.
--   * Contains no reveal or conceal case, retired `PairedCast` abstraction,
--     quotient case, recursive dispatcher, postulate, hole, or option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv)
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
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (paired-wideningᵀ; prefix-reflⁱ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-⟨⟩)
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
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions-reflects-Inert)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
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


active-paired-widening-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ N′ : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion} {μ μ′ : ModeEnv}
    {s s′ t : ImprecisionShape}
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
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  widening ⊢ᶜ c ⦂ s →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  widening ⊢ᶜ c′ ⦂ s′ →
  s ； ⌊ q ⌋ ≋ t →
  ⌊ p ⌋ ； s′ ≋ t →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ p q s s′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  V′ ⟨ c′ ⟩ —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′}
    {χ = keep} {ρ = ρ} q
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    with catchup coherent exclusive unique wfL
      (runtime-⟨⟩ ok-source) vV′
      (runtime-value-no• (runtime-⟨⟩ ok-target) vV′) M⊑V′
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ
      (sourceCatchup
        (weakIndexedResult (catchupIndexedResult caught))))
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW) | refl | refl
    with paired-widening-evidence-transportᵀ
      prefix-reflⁱ
      (weakIndexedResult (catchupIndexedResult caught))
      (weakIndexedTypeCoherence (catchupIndexedResult caught))
      final-unique
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible
active-paired-widening-root-proofᵀ
    catchup synchronize coherent exclusive unique wfL wfR
    ok-source ok-target vV′ noninert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑V′ target-root
    | world-coherent-left-indexed-catchup
        caught lineage final-coherent final-exclusive final-unique final-wfL
    | inj₁ (vW , noW) | refl | refl
    | μˢ , μᵗ , sˢ , sᵗ , t′ ,
      modeˢ , seal★ˢ , cˢ⊑ , cˢ-shape ,
      modeᵗ , seal★ᵗ , cᵗ⊑ , cᵗ-shape ,
      left-square′ , right-square′ , compatible′ =
  world-coherent-left-silent-then-outcomeᵀ
    framed-silent framed-lineage final-outcome
  where
  indexed = catchupIndexedResult caught
  inner = weakIndexedResult indexed
  final-inner = canonicalIndexedResults indexed
  final-relation =
    paired-wideningᵀ
      modeˢ seal★ˢ cˢ⊑ cˢ-shape
      modeᵗ seal★ᵗ cᵗ⊑ cᵗ-shape
      left-square′ right-square′ compatible′ final-inner
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
    synchronize-paired-widening synchronize
      final-coherent final-exclusive final-unique final-wfL final-wfR
      (ok-no (no•-⟨⟩ noW)) ok-target
      vW noW vV′ noV′ final-noninert
      modeˢ seal★ˢ cˢ⊑ cˢ-shape
      modeᵗ seal★ᵗ cᵗ⊑ cᵗ-shape
      left-square′ right-square′ compatible′
      final-inner target-root
