module
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepApplicationCrossedCaseProof
  where

-- File Charter:
--   * Proves the crossed application-right target-step clause in which the
--     source function must first catch up to the target function value.
--   * Uses lockstep source-no-bullet/target-runtime sibling transport, frames
--     the caught silent prefix, simulates the argument step, and composes.
--   * Contains no recursive dispatcher implementation, aggregate embedding
--     reconstruction, postulate, hole, permissive option, or wrapper alias.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  ; ↠-refl
  ; _—↠[_]_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; ok-no
  ; ok-·₁
  ; _·_
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; ·⊑·ᵀ
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( ·₁-blame-tail
  ; weak-indexed-arrow-resultᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalArrowResults
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
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
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
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
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTerms-preserves-No•
  ; ·₁-↠
  )
open import QuotientedTermImprecision using
  ( nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; worldCatchupAssumptionMembershipUnique
  ; worldCatchupCoherence
  ; worldCatchupResult
  ; worldCatchupSourceNameExclusive
  ; worldCatchupSourceStoreWf
  ; worldCatchupStoreLineage
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  using
  ( WorldCoherentRightOneStepApplicationFrames
  ; rightStepApplicationRightFrame
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)


private
  source-value-or-blame-runtime :
    ∀ {M} →
    ((Value M × No• M) ⊎ M ≡ blame) →
    RuntimeOK M
  source-value-or-blame-runtime (inj₁ (vM , noM)) =
    ok-no noM
  source-value-or-blame-runtime (inj₂ refl) =
    ok-no no•-blame

  left-silent-application-runtime-sibling-frameᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ R R′ : Term} {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    No• R →
    (caught : WorldCoherentLeftCatchupIndexedResult
      {N = L} {V′ = L′} {ρ = ρ} (pA ↦ pB)) →
    let inner =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ applyTerms (sourceChanges inner) R
        ⊑ applyTerms (targetTailChanges inner) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy keep A′)
      ∶ transportType inner pA →
    LeftSilentIndexedResult
      {N = L · R} {V′ = L′ · R′} {ρ = ρ} pB
  left-silent-application-runtime-sibling-frameᵀ
      {ρ = ρ} {L = L} {L′ = L′} {R = R} {R′ = R′}
      {B = B} {B′ = B′}
      {pA = pA} {pB = pB}
      noR
      (world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage coherent exclusive unique wfL)
      R⊑R′ =
    left-silent-indexed
      (weak-indexed-result framed (relatedResults framed)
        framed-transport framed-coherence)
      (left-silent-invariant refl refl)
      (ok-·₁ final-runtime
        (applyTerms-preserves-No• (sourceChanges inner) noR))
    where
    inner = weakIndexedResult indexed
    arrow = weak-indexed-arrow-resultᵀ indexed
    L⊑L′ = canonicalArrowResults arrow

    final-runtime =
      source-value-or-blame-runtime final

    framed : WeakOneStepResult ρ
      (L · R) (L′ · R′) B B′ keep
    framed =
      weak-step-result
        (sourceChanges inner)
        []
        (sourceResult inner · applyTerms (sourceChanges inner) R)
        (targetResult inner · R′)
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
        (transportType inner pB)
        (·₁-↠ noR (sourceCatchup inner))
        ↠-refl
        (sourceStoreResult inner)
        (targetStoreResult inner)
        (·⊑·ᵀ L⊑L′ R⊑R′)

    framed-transport : WeakOneStepTransport framed
    framed-transport =
      weak-step-transport
        (transportNo•Terms (weakIndexedTransport indexed))

    framed-coherence : WeakOneStepTypeCoherence framed
    framed-coherence =
      weak-step-type-coherence
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
          (weakIndexedTypeCoherence indexed))


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


world-coherent-right-one-step-application-right-crossed-caseᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightOneStepApplicationFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ R R′ R₁′ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK L →
  Value L′ →
  No• L′ →
  No• R →
  RuntimeOK R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ R ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ R′ ⦂ A′ →
  R′ —→[ χ ] R₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · R} {N′ = applyTerm χ L′ · R₁′}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
world-coherent-right-one-step-application-right-crossed-caseᵀ
    sibling-catchup recursive frames
    {L = L}
    prefix coherent exclusive unique wfL wfR
    okL vL′ noL′ noR okR′ L⊑L′ R⊑R′ R⊢ R′⊢ R′→
    with sibling-catchup prefix coherent exclusive unique wfL
      okL vL′ noL′ L⊑L′ noR okR′ R⊑R′ R⊢ R′⊢
world-coherent-right-one-step-application-right-crossed-caseᵀ
    sibling-catchup recursive frames
    {L = L}
    prefix coherent exclusive unique wfL wfR
    okL vL′ noL′ noR okR′ L⊑L′ R⊑R′ R⊢ R′⊢ R′→
    | caught@(world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage final-coherent final-exclusive final-unique final-wfL)
      , final-R
    with final
world-coherent-right-one-step-application-right-crossed-caseᵀ
    sibling-catchup recursive frames
    {L = L}
    prefix coherent exclusive unique wfL wfR
    okL vL′ noL′ noR okR′ L⊑L′ R⊑R′ R⊢ R′⊢ R′→
    | caught@(world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage final-coherent final-exclusive final-unique final-wfL)
      , final-R
    | inj₂ source-is-blame =
  world-indexed-outcome-source-blame
    (·₁-blame-tail noR
      (subst
        (λ X → L —↠[ sourceChanges inner ] X)
        source-is-blame (sourceCatchup inner)))
  where
  inner = weakIndexedResult indexed
world-coherent-right-one-step-application-right-crossed-caseᵀ
    sibling-catchup recursive frames
    {L = L}
    prefix coherent exclusive unique wfL wfR
    okL vL′ noL′ noR okR′ L⊑L′ R⊑R′ R⊢ R′⊢ R′→
    | caught@(world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage final-coherent final-exclusive final-unique final-wfL)
      , final-R
    | inj₁ (vV , noV) =
  world-coherent-left-silent-then-outcomeᵀ
    first-silent framed-lineage framed-outcome
  where
  inner = weakIndexedResult indexed
  arrow = weak-indexed-arrow-resultᵀ indexed
  final-L = canonicalArrowResults arrow

  first-silent =
    left-silent-application-runtime-sibling-frameᵀ
      noR caught final-R

  framed-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  final-wfR = final-right-store-wf inner refl wfR

  recursive-R =
    recursive prefix-reflⁱ final-coherent final-exclusive final-unique
      final-wfL final-wfR
      (ok-no (applyTerms-preserves-No•
        (sourceChanges inner) noR))
      okR′ final-R
      (nu-term-imprecision-source-typing final-R)
      (nu-term-imprecision-target-typing final-R)
      R′→

  framed-outcome =
    rightStepApplicationRightFrame frames
      vV noV vL′ noL′ final-L recursive-R
