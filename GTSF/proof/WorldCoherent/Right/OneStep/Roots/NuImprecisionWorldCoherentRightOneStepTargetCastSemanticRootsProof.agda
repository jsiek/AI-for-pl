module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastSemanticRootsProof
  where

-- File Charter:
--   * Proves the five semantic target-cast roots for world-coherent
--     target-oriented one-step simulation.
--   * Catches the arbitrary source up at the final source-only world,
--     terminalizes the transported target cast there, removes the observed
--     pure target root, and composes the two catch-up phases.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or reconstruction of exact QTI cast evidence.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; inst
  ; seal
  ; unseal
  ; _!
  ; _？
  ; _︔_
  )
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( keep
  ; _—→_
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import
  proof.Catchup.Simulation.NuImprecisionKeepCastFrameSupport
  using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-compose-type-to-nested≅
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silentᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( weak-one-step-index-resultᵀ
  )
open import proof.Core.Equality.HeterogeneousEqualityTransport using
  ( subst²-to-≅
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentResult
  ; LeftSilentIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; sourceResult
  ; sourceCtxResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetIsUnchanged
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTailIsEmpty
  ; targetTypeResult
  ; transportArrowCoherent
  ; transportAllBody
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
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
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Target.Core.NuImprecisionTargetBlameCatchup
  using (left-catchup-target-blameᵀ)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using
  ( rightCatchupIndexedResult
  ; rightCatchupTargetValue
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition
  using (world-coherent-left-silent-then-right-valueᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsDef
  using
  ( WorldCoherentRightOneStepTargetCastSemanticRoots
  ; rightStepTargetNarrowSequenceRoot
  ; rightStepTargetNarrowUntagRoot
  ; rightStepTargetWidenInstantiationRoot
  ; rightStepTargetWidenSequenceRoot
  ; rightStepTargetWidenUnsealRoot
  )
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetNarrowFrame
  ; rightTargetWidenFrame
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualLemma
  using (world-coherent-right-target-pure-step-residualᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupResult
  )
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalDef
  using (WorldCoherentRightValueTerminalᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  catchup-source-runtime :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (catchup : LeftCatchupIndexedResult
      {N = M} {V′ = V′} {ρ = ρ} p) →
    RuntimeOK
      (sourceResult
        (weakIndexedResult (catchupIndexedResult catchup)))
  catchup-source-runtime catchup
      with sourceIsValueOrBlame (catchupIndexedInvariant catchup)
  catchup-source-runtime catchup | inj₁ (vV , noV) = ok-no noV
  catchup-source-runtime catchup | inj₂ refl = ok-no no•-blame

  final-right-store-wf :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A B : Ty}
      (first : WeakOneStepResult ρ M V′ A B keep) →
    targetTailChanges first ≡ [] →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    StoreWf (resultRightCtx first) (rightStoreⁱ (resultStore first))
  final-right-store-wf {ρ = ρ} first refl wfR =
    subst (StoreWf (resultRightCtx first))
      (sym (targetStoreResult first))
      (subst (λ Δ → StoreWf Δ (rightStoreⁱ ρ))
        (sym (targetCtxResult first)) wfR)

  final-seal-mode :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A B : Ty}
      (first : WeakOneStepResult ρ M V′ A B keep)
      {μ : ModeEnv} →
    targetTailChanges first ≡ [] →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    SealModeStore★ μ (rightStoreⁱ (resultStore first))
  final-seal-mode first {μ = μ} refl seal★ =
    subst (SealModeStore★ μ)
      (sym (targetStoreResult first)) seal★

  final-narrow-typing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ : Ty}
      (first : WeakOneStepResult ρ M V′ A A′ keep)
      {μ : ModeEnv} {c : Coercion} {B′ : Ty} →
    targetTailChanges first ≡ [] →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊒ B′ →
    μ ∣ resultRightCtx first ∣ rightStoreⁱ (resultStore first)
      ⊢ c ∶ A′ ⊒ B′
  final-narrow-typing {ρ = ρ} {A′ = A′}
      first {μ = μ} {c = c} {B′ = B′} refl c⊒ =
    subst (λ Σ → μ ∣ resultRightCtx first ∣ Σ ⊢ c ∶ A′ ⊒ B′)
      (sym (targetStoreResult first))
      (subst (λ Δ → μ ∣ Δ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊒ B′)
        (sym (targetCtxResult first)) c⊒)

  final-widen-typing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ : Ty}
      (first : WeakOneStepResult ρ M V′ A A′ keep)
      {μ : ModeEnv} {c : Coercion} {B′ : Ty} →
    targetTailChanges first ≡ [] →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊑ B′ →
    μ ∣ resultRightCtx first ∣ rightStoreⁱ (resultStore first)
      ⊢ c ∶ A′ ⊑ B′
  final-widen-typing {ρ = ρ} {A′ = A′}
      first {μ = μ} {c = c} {B′ = B′} refl c⊑ =
    subst (λ Σ → μ ∣ resultRightCtx first ∣ Σ ⊢ c ∶ A′ ⊑ B′)
      (sym (targetStoreResult first))
      (subst (λ Δ → μ ∣ Δ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊑ B′)
        (sym (targetCtxResult first)) c⊑)

  transported-narrow-triangle :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
      (first : WeakOneStepResult ρ M V′ A A′ keep)
      (coherence : WeakOneStepTypeCoherence first)
      (shape : ImprecisionShape) →
    ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
    ⌊ transportType first q ⌋ ； shape
      ≋ ⌊ transportType first p ⌋
  transported-narrow-triangle {p = p} {q = q}
      first coherence shape triangle
      rewrite transportShapeCoherent
        coherence q
      | transportShapeCoherent
        coherence p =
    triangle

  transported-widen-triangle :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
      (first : WeakOneStepResult ρ M V′ A A′ keep)
      (coherence : WeakOneStepTypeCoherence first)
      (shape : ImprecisionShape) →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    ⌊ transportType first p ⌋ ； shape
      ≋ ⌊ transportType first q ⌋
  transported-widen-triangle {p = p} {q = q}
      first coherence shape triangle
      rewrite transportShapeCoherent coherence p
      | transportShapeCoherent coherence q =
    triangle

  narrow-square :
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentRightValueTerminalᵀ →
    WorldCoherentRightTargetCastTerminalization →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ N′ : Term} {A A′ B′ : Ty}
      {c : Coercion} {μ : ModeEnv}
      {shape : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK V′ →
    RuntimeOK (V′ ⟨ c ⟩) →
    Value V′ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊒ B′ →
    CastShape.narrowing CastShape.⊢ᶜ c ⦂ shape →
    ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
    V′ ⟨ c ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  narrow-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊒ c-shape comp M⊑V′ root
      with catchup coherent exclusive unique wfL okM vV′
        (runtime-value-no• okV′ vV′) M⊑V′
  narrow-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊒ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  narrow-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊒ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (sourceCatchup (weakIndexedResult (catchupIndexedResult caught)))
  narrow-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊒ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty (silentInvariant
             (catchupIndexedInvariant caught))
         | targetIsUnchanged (silentInvariant
             (catchupIndexedInvariant caught))
  narrow-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊒ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl =
    world-coherent-left-silent-then-right-valueᵀ
      framed-silent framed-lineage residual
    where
    first-indexed = catchupIndexedResult caught
    first = weakIndexedResult first-indexed
    first-coherence = weakIndexedTypeCoherence first-indexed

    noV′ = runtime-value-no• okV′ vV′
    final-wfR = final-right-store-wf first refl wfR
    final-seal★ = final-seal-mode first refl seal★
    final-c⊒ = final-narrow-typing first refl c⊒
    final-comp =
      transported-narrow-triangle
        first first-coherence shape comp

    inner-terminal =
      terminal prefix-reflⁱ final-coherent final-exclusive final-unique
        final-wfR vW noW vV′ noV′
        (canonicalIndexedResults first-indexed)

    outer-terminal =
      rightTargetNarrowFrame terminalization
        prefix-reflⁱ final-coherent final-exclusive final-unique final-wfR
        okCast vW noW mode final-seal★ final-c⊒ c-shape final-comp
        (canonicalIndexedResults first-indexed) inner-terminal

    residual =
      world-coherent-right-target-pure-step-residualᵀ
        root outer-terminal

    framed-relation =
      ⊑cast⊒ᵀ mode final-seal★ final-c⊒
        (canonicalIndexedResults first-indexed)
        (transportType first _)
        c-shape final-comp

    framed-raw =
      weak-one-step-target-cast-frameᵀ first framed-relation

    framed-indexed =
      weak-indexed-result framed-raw (relatedResults framed-raw)
        (weak-one-step-target-cast-frame-transportᵀ
          first framed-relation (weakIndexedTransport first-indexed))
        (weak-one-step-target-cast-frame-coherenceᵀ
          first framed-relation (weakIndexedTypeCoherence first-indexed))

    framed-silent =
      left-silent-indexed
        framed-indexed
        (left-silent-invariant refl refl)
        (ok-no noW)

    framed-lineage =
      weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage)

  widen-square :
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentRightValueTerminalᵀ →
    WorldCoherentRightTargetCastTerminalization →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ N′ : Term} {A A′ B′ : Ty}
      {c : Coercion} {μ : ModeEnv}
      {shape : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK V′ →
    RuntimeOK (V′ ⟨ c ⟩) →
    Value V′ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A′ ⊑ B′ →
    CastShape.widening CastShape.⊢ᶜ c ⦂ shape →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
    V′ ⟨ c ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  widen-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊑ c-shape comp M⊑V′ root
      with catchup coherent exclusive unique wfL okM vV′
        (runtime-value-no• okV′ vV′) M⊑V′
  widen-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊑ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  widen-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊑ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (sourceCatchup (weakIndexedResult (catchupIndexedResult caught)))
  widen-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊑ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty (silentInvariant
             (catchupIndexedInvariant caught))
         | targetIsUnchanged (silentInvariant
             (catchupIndexedInvariant caught))
  widen-square catchup terminal terminalization {shape = shape}
      coherent exclusive unique wfL wfR okM okV′ okCast vV′
      mode seal★ c⊑ c-shape comp M⊑V′ root
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl =
    world-coherent-left-silent-then-right-valueᵀ
      framed-silent framed-lineage residual
    where
    first-indexed = catchupIndexedResult caught
    first = weakIndexedResult first-indexed
    first-coherence = weakIndexedTypeCoherence first-indexed

    noV′ = runtime-value-no• okV′ vV′
    final-wfR = final-right-store-wf first refl wfR
    final-seal★ = final-seal-mode first refl seal★
    final-c⊑ = final-widen-typing first refl c⊑
    final-comp =
      transported-widen-triangle first first-coherence shape comp

    inner-terminal =
      terminal prefix-reflⁱ final-coherent final-exclusive final-unique
        final-wfR vW noW vV′ noV′
        (canonicalIndexedResults first-indexed)

    outer-terminal =
      rightTargetWidenFrame terminalization
        prefix-reflⁱ final-coherent final-exclusive final-unique final-wfR
        okCast vW noW mode final-seal★ final-c⊑ c-shape final-comp
        (canonicalIndexedResults first-indexed) inner-terminal

    residual =
      world-coherent-right-target-pure-step-residualᵀ
        root outer-terminal

    framed-relation =
      ⊑cast⊑ᵀ mode final-seal★ final-c⊑
        (canonicalIndexedResults first-indexed)
        (transportType first _)
        c-shape final-comp

    framed-raw =
      weak-one-step-target-cast-frameᵀ first framed-relation

    framed-indexed =
      weak-indexed-result framed-raw (relatedResults framed-raw)
        (weak-one-step-target-cast-frame-transportᵀ
          first framed-relation (weakIndexedTransport first-indexed))
        (weak-one-step-target-cast-frame-coherenceᵀ
          first framed-relation (weakIndexedTypeCoherence first-indexed))

    framed-silent =
      left-silent-indexed framed-indexed
        (left-silent-invariant refl refl) (ok-no noW)

    framed-lineage =
      weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage)


world-coherent-right-one-step-target-cast-semantic-roots-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightValueTerminalᵀ →
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightOneStepTargetCastSemanticRoots
world-coherent-right-one-step-target-cast-semantic-roots-proofᵀ
    catchup terminal terminalization =
  record
    { rightStepTargetNarrowSequenceRoot =
        λ
          { coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊒ c-shape comp inner
              root@(β-seq vV) →
            narrow-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast vV
              mode seal★ c⊒ c-shape comp inner root
          ; coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊒ c-shape comp inner
              blame-⟨⟩ →
            world-indexed-outcome-source-blame
              (proj₂ (left-catchup-target-blameᵀ okM inner))
          }
    ; rightStepTargetNarrowUntagRoot =
        λ
          { coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊒ c-shape comp inner
              root@(tag-untag-ok vV) →
            narrow-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast
              (vV ⟨ _ ! ⟩) mode seal★ c⊒ c-shape comp inner root
          ; coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊒ c-shape comp inner
              root@(tag-untag-bad vV G≢H) →
            narrow-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast
              (vV ⟨ _ ! ⟩) mode seal★ c⊒ c-shape comp inner root
          }
    ; rightStepTargetWidenSequenceRoot =
        λ
          { coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊑ c-shape comp inner
              root@(β-seq vV) →
            widen-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast vV
              mode seal★ c⊑ c-shape comp inner root
          ; coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊑ c-shape comp inner
              blame-⟨⟩ →
            world-indexed-outcome-source-blame
              (proj₂ (left-catchup-target-blameᵀ okM inner))
          }
    ; rightStepTargetWidenInstantiationRoot =
        λ
          { coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊑ c-shape comp inner
              root@(β-inst vV) →
            widen-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast vV
              mode seal★ c⊑ c-shape comp inner root
          ; coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊑ c-shape comp inner
              blame-⟨⟩ →
            world-indexed-outcome-source-blame
              (proj₂ (left-catchup-target-blameᵀ okM inner))
          }
    ; rightStepTargetWidenUnsealRoot =
        λ
          { coherent exclusive unique wfL wfR okM okCast
              mode seal★ c⊑ c-shape comp inner
              root@(seal-unseal vV) →
            widen-square catchup terminal terminalization
              coherent exclusive unique wfL wfR okM
              (runtime-⟨⟩ okCast) okCast
              (vV ⟨ seal _ _ ⟩)
              mode seal★ c⊑ c-shape comp inner root
          }
    }
