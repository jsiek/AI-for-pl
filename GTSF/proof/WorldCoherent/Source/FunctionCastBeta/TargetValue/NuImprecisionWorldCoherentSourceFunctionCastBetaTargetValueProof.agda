module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueProof
  where

-- File Charter:
--   * Reduces source function-cast beta against a target function value to
--     the value/value terminal by catching up the target argument.
--   * Frames and composes the target-only argument trace exactly once.
--   * Contains no coercion algebra, recursive measure, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import Coercions as C
open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTerms; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ok-no
  ; ok-·₂
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-index-resultᵀ
  ; weak-one-step-·₂-indexed-frameᵀ
  ; weak-result-transport-arrow-termsᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceResult
  ; sourceTypeResult
  ; targetResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Source.Core.NuImprecisionSourceSilentCompositionDef using
  ( SourceSilentComposition
  ; sourceSilentAssumptionMembershipUnique
  ; sourceSilentChangesExact
  ; sourceSilentResult
  ; sourceSilentResultExact
  ; sourceSilentSourceNameExclusive
  ; sourceSilentStoreLineage
  ; sourceSilentTransport
  ; sourceSilentTypeCoherence
  ; sourceSilentWorldCoherent
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof using
  (target-function-cast-spine-rank-applyTerms)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  ; worldRightCatchupTargetStoreWf
  )
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueDef
  using
  ( WorldCoherentSourceFunctionCastBetaTargetValueᵀ
  ; WorldCoherentSourceFunctionCastBetaTargetValuesᵀ
  )
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueRankedDef
  using
  ( WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ
  ; WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-·₂; value-runtime-No•)
open import proof.Core.Properties.ReductionProperties using
  (applyTerms-preserves-No•; applyTerms-preserves-Value)
open import proof.Core.Properties.TypePreservation using (term-weaken)

world-coherent-source-function-cast-beta-target-value-at-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  ∀ {n} →
  WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ n →
  WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n
world-coherent-source-function-cast-beta-target-value-at-proofᵀ
    right-catchup composition target-values
    {V = V} {W = W} {L′ = L′} {R′ = R′} {c = c} {d = d}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ target-rank
    with right-catchup prefix coherent exclusive unique wfR
      (runtime-·₂ vL′ okM′)
      vW source-argument-no argument-related
  where
  source-function-value = vV ⟨ c C.↦ d ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  source-argument-no =
    value-runtime-No• vW (runtime-·₂ source-function-value okM)
  target-function-no =
    value-runtime-No• vL′ (runtime-·₁ okM′)
world-coherent-source-function-cast-beta-target-value-at-proofᵀ
    right-catchup composition target-values
    {V = V} {W = W} {L′ = L′} {R′ = R′} {c = c} {d = d}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ target-rank
    | caught
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult caught
world-coherent-source-function-cast-beta-target-value-at-proofᵀ
    right-catchup composition target-values
    {ρ⁺ = ρ⁺} {V = V} {W = W} {L′ = L′} {R′ = R′}
    {c = c} {d = d} {B = B} {B′ = B′} {pB = pB}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ target-rank
    | caught | refl | refl =
  world-coherent-source-one-step-indexed
    combined-indexed
    combined-lineage combined-changes combined-result combined-world
    combined-exclusive combined-unique
  where
  catchup = worldRightCatchupResult caught
  argument-indexed = rightCatchupIndexedResult catchup
  argument-result = weakIndexedResult argument-indexed
  tail = targetTailChanges argument-result

  source-function-value = vV ⟨ c C.↦ d ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  source-argument-no =
    value-runtime-No• vW (runtime-·₂ source-function-value okM)
  target-function-no =
    value-runtime-No• vL′ (runtime-·₁ okM′)

  source-function⊢⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      source-function-no
      (nu-term-imprecision-source-typing function-related)

  target-function⊢⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      target-function-no
      (nu-term-imprecision-target-typing function-related)

  function-related⁺ =
    allocation-prefixᵀ prefix function-related
      source-function⊢⁺ target-function⊢⁺

  framed-indexed =
    weak-one-step-·₂-indexed-frameᵀ
      source-function-value source-function-no vL′ target-function-no
      function-related⁺ argument-indexed
      (weakIndexedTransport (rightCatchupIndexedResult catchup))
      (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed = weakIndexedResult framed-indexed

  framed-transport =
    weak-step-transport
      (transportNo•Terms (weakIndexedTransport (rightCatchupIndexedResult catchup)))

  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)))
      (transportAllCoherent (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)))

  framed-lineage : WeakOneStepStoreLineage framed
  framed-lineage =
    weak-step-store-lineage
      (lineageStore caught-lineage)
      (lineageEmbedding caught-lineage)
      (lineagePrefix caught-lineage)
    where
    caught-lineage = worldRightCatchupStoreLineage caught

  function-final =
    weak-result-transport-arrow-termsᵀ
      argument-result (weakIndexedTransport (rightCatchupIndexedResult catchup))
      (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))
      source-function-no target-function-no function-related⁺

  target-function-value-final =
    applyTerms-preserves-Value tail vL′
  target-function-no-final =
    applyTerms-preserves-No• tail target-function-no
  target-function-rank-final =
    trans
      (target-function-cast-spine-rank-applyTerms tail vL′)
      target-rank

  phase-two :
    WorldCoherentSourceOneStepIndexedResult
      {M = (V ⟨ c C.↦ d ⟩) · W}
      {M′ = applyTerms tail L′ · targetResult argument-result}
      {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
      {A = B}
      {B = applyTys tail B′}
      {χ = keep} {ρ = resultStore argument-result}
      (transportType argument-result pB)
  phase-two =
    target-values
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      okM
      (ok-·₂ target-function-value-final target-function-no-final
        (ok-no (rightCatchupTargetNoBullet catchup)))
      function-final
      (canonicalIndexedResults argument-indexed)
      vV vW target-function-value-final
      (rightCatchupTargetValue catchup)
      target-function-rank-final

  phase-two-indexed = sourceStepIndexedResult phase-two
  phase-two-result = weakIndexedResult phase-two-indexed

  combined :
    WeakOneStepResult ρ⁺
      ((V ⟨ c C.↦ d ⟩) · W) (L′ · R′) B B′ keep
  combined =
    sourceSilentResult composition framed refl refl phase-two-result

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition framed refl refl phase-two-result
      (sourceStepAssumptionMembershipUnique phase-two)

  combined-type-eq :
    subst
      (λ T → resultCtx combined ∣ resultLeftCtx combined
        ⊢ _ ⊑ T ⊣ resultRightCtx combined)
      (targetTypeResult combined)
      (subst
        (λ S → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ resultTargetType combined ⊣ resultRightCtx combined)
        (sourceTypeResult combined)
        (resultType combined))
    ≡ transportType combined pB
  combined-type-eq =
    assumption-membership-unique→precision-index-unique
      combined-unique _ (transportType combined pB)

  combined-transport =
    sourceSilentTransport composition framed refl refl phase-two-result
      framed-transport (weakIndexedTransport (sourceStepIndexedResult phase-two))

  combined-coherence =
    sourceSilentTypeCoherence composition framed refl refl phase-two-result
      framed-coherence (weakIndexedTypeCoherence (sourceStepIndexedResult phase-two))

  combined-indexed : WeakOneStepIndexedResult pB
  combined-indexed =
    weak-one-step-index-resultᵀ combined combined-type-eq
      combined-transport combined-coherence

  combined-lineage =
    sourceSilentStoreLineage composition framed refl refl phase-two-result
      framed-lineage (sourceStepStoreLineage phase-two)

  combined-changes =
    sourceSilentChangesExact composition framed refl refl phase-two-result
      (sourceStepChangesExact phase-two)

  combined-result =
    sourceSilentResultExact composition framed refl refl phase-two-result
      (sourceStepResultExact phase-two)

  combined-world =
    sourceSilentWorldCoherent composition framed refl refl phase-two-result
      (sourceStepWorldCoherent phase-two)

  combined-exclusive =
    sourceSilentSourceNameExclusive
      composition framed refl refl phase-two-result
      (sourceStepSourceNameExclusive phase-two)


private
  target-values-atᵀ :
    WorldCoherentSourceFunctionCastBetaTargetValuesᵀ →
    ∀ {n} →
    WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ n
  target-values-atᵀ target-values
      coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′ target-rank =
    target-values coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vL′ vR′


world-coherent-source-function-cast-beta-target-value-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceFunctionCastBetaTargetValuesᵀ →
  WorldCoherentSourceFunctionCastBetaTargetValueᵀ
world-coherent-source-function-cast-beta-target-value-proofᵀ
    right-catchup composition target-values
    {V = V} {W = W} {L′ = L′} {R′ = R′} {c = c} {d = d}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ =
  world-coherent-source-function-cast-beta-target-value-at-proofᵀ
    right-catchup composition (target-values-atᵀ target-values)
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′ refl
