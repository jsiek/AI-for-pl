module
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrimitiveCrossedCaseProof
  where

-- File Charter:
--   * Proves the crossed primitive-right target-step clause in which the
--     source left operand first catches up to the target left value.
--   * Carries the right-operand relation through that catch-up, normalizes
--     transported natural-number indices, simulates, frames, and composes.
--   * Contains no recursive dispatcher implementation, aggregate embedding
--     reconstruction, postulate, hole, permissive option, or wrapper alias.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; sym)

open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  ; _—↠[_]_
  ; _—→[_]_
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
  ; blame
  ; no•-blame
  ; ok-no
  ; ok-⊕₁
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( TyCtx
  ; `ℕ
  ; ‵_
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTys-ℕ
  )
open import proof.OneStep.NuImprecisionOneStepPrimitiveFrames using
  ( target-ℕ-result
  ; transport-idι-to-ℕ
  ; transport-term-to-ℕᵀ
  ; weak-one-step-left-silent-⊕₁-transported-frameᵀ
  ; weak-one-step-⊕₁-source-blame-frameᵀ
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentOutcomeTransportProof
  using (world-coherent-indexed-outcome-transport-typesᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  using
  ( WorldCoherentRightOneStepPrimitiveFrames
  ; rightStepPrimitiveRightFrame
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

  left-silent-primitive-runtime-sibling-frameᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ R R′ : Term} →
    No• R →
    (caught : WorldCoherentLeftCatchupIndexedResult
      {N = L} {V′ = L′}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {ρ = ρ} idι) →
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
      ⦂ applyTys (sourceChanges inner) (‵ `ℕ)
        ⊑ applyTys (targetTailChanges inner)
            (applyTy keep (‵ `ℕ))
      ∶ transportType inner idι →
    LeftSilentIndexedResult
      {N = L ⊕[ addℕ ] R}
      {V′ = L′ ⊕[ addℕ ] R′}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {ρ = ρ} idι
  left-silent-primitive-runtime-sibling-frameᵀ
      {ρ = ρ} {R = R}
      noR
      (world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage coherent exclusive unique wfL)
      R⊑R′ =
    left-silent-indexed
      (weak-one-step-left-silent-⊕₁-transported-frameᵀ
        noR indexed (left-silent-invariant refl refl) R⊑R′)
      (left-silent-invariant refl refl)
      (ok-⊕₁ (source-value-or-blame-runtime final)
        (applyTerms-preserves-No•
          (sourceChanges inner) noR))
    where
    inner = weakIndexedResult indexed

  final-right-store-wf :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term}
      (inner :
        WeakOneStepResult ρ M V′ (‵ `ℕ) (‵ `ℕ) keep) →
    targetTailChanges inner ≡ [] →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    StoreWf (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
  final-right-store-wf {ρ = ρ} inner refl wfR =
    subst (StoreWf (resultRightCtx inner))
      (sym (targetStoreResult inner))
      (subst (λ Δ → StoreWf Δ (rightStoreⁱ ρ))
        (sym (targetCtxResult inner)) wfR)


world-coherent-right-one-step-primitive-right-crossed-caseᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightOneStepPrimitiveFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ R R′ R₁′ : Term} {χ : StoreChange} →
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
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ R ⦂ ‵ `ℕ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ R′ ⦂ ‵ `ℕ →
  R′ —→[ χ ] R₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] R}
    {N′ = applyTerm χ L′ ⊕[ addℕ ] R₁′}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = χ} {ρ = ρ} idι
world-coherent-right-one-step-primitive-right-crossed-caseᵀ
    sibling-catchup recursive frames
    {L = L}
    prefix coherent exclusive unique wfL wfR
    okL vL′ noL′ noR okR′ L⊑L′ R⊑R′ R⊢ R′⊢ R′→
    with sibling-catchup prefix coherent exclusive unique wfL
      okL vL′ noL′ L⊑L′ noR okR′ R⊑R′ R⊢ R′⊢
world-coherent-right-one-step-primitive-right-crossed-caseᵀ
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
world-coherent-right-one-step-primitive-right-crossed-caseᵀ
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
    (weak-one-step-⊕₁-source-blame-frameᵀ noR
      (subst
        (λ X → L —↠[ sourceChanges inner ] X)
        source-is-blame (sourceCatchup inner)))
  where
  inner = weakIndexedResult indexed
world-coherent-right-one-step-primitive-right-crossed-caseᵀ
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
  source-ℕ = applyTys-ℕ (sourceChanges inner)
  target-ℕ = target-ℕ-result keep []

  final-L-ℕ =
    transport-term-to-ℕᵀ source-ℕ target-ℕ
      (canonicalIndexedResults indexed)

  final-R-ℕ =
    transport-term-to-ℕᵀ source-ℕ target-ℕ final-R

  first-silent =
    left-silent-primitive-runtime-sibling-frameᵀ
      noR caught final-R

  framed-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  final-wfR = final-right-store-wf inner refl wfR

  recursive-R-ℕ =
    recursive prefix-reflⁱ final-coherent final-exclusive final-unique
      final-wfL final-wfR
      (ok-no (applyTerms-preserves-No•
        (sourceChanges inner) noR))
      okR′ final-R-ℕ
      (nu-term-imprecision-source-typing final-R-ℕ)
      (nu-term-imprecision-target-typing final-R-ℕ)
      R′→

  framed-outcome-ℕ =
    rightStepPrimitiveRightFrame frames
      vV noV vL′ noL′ final-L-ℕ recursive-R-ℕ

  framed-outcome =
    world-coherent-indexed-outcome-transport-typesᵀ
      source-ℕ target-ℕ
      (transport-idι-to-ℕ source-ℕ target-ℕ
        (transportType inner idι))
      framed-outcome-ℕ
