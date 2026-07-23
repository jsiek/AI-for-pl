module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectProof
  where

-- File Charter:
--   * Reduces direct target function-cast scheduling to the value-argument
--     terminal by catching up the target argument first.
--   * Frames and composes that source-silent argument trace exactly once.
--   * Contains no function-cast spine recursion, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import ImprecisionWf using (_↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTerms; applyTys; bind; keep)
open import NuTermImprecision using
  (StoreImp; ctx-imp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-ƛ
  ; no•-⟨⟩
  ; ok-no
  ; ok-·₂
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (_⇒_)
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
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastRankedDef
  using
  ( WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ
  ; WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ
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
  ( applyCoercions
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  )
open import proof.Core.Properties.TypePreservation using (term-weaken)


private
  lambda-runtime-body-No• :
    ∀ {N} →
    RuntimeOK (ƛ N) →
    No• N
  lambda-runtime-body-No• (ok-no (no•-ƛ noN)) = noN

  cast-value-body-No• :
    ∀ {W c} →
    No• (W ⟨ c ⟩) →
    No• W
  cast-value-body-No• (no•-⟨⟩ noW) = noW

  applyTerms-function-cast :
    ∀ χs W c d →
    applyTerms χs (W ⟨ c C.↦ d ⟩) ≡
      applyTerms χs W ⟨
        applyCoercions χs c C.↦ applyCoercions χs d ⟩
  applyTerms-function-cast [] W c d = refl
  applyTerms-function-cast (keep ∷ χs) W c d =
    applyTerms-function-cast χs W c d
  applyTerms-function-cast (bind A ∷ χs) W c d =
    applyTerms-function-cast χs _ _ _


world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ :
  ∀ {n} →
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ n →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n
world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ
    right-catchup composition value-terminal
    {N = N} {V = V} {W = W} {R′ = R′} {c = c} {d = d}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW target-rank
    with right-catchup prefix coherent exclusive unique wfR
      (runtime-·₂ target-function-value okM′)
      vV source-argument-no argument-related
  where
  source-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM)
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
  target-function-value = vW ⟨ c C.↦ d ⟩
world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ
    right-catchup composition value-terminal
    {N = N} {V = V} {W = W} {R′ = R′} {c = c} {d = d}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW target-rank
    | caught
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult caught
world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ
    {n = n} right-catchup composition value-terminal
    {ρ⁺ = ρ⁺} {N = N} {V = V} {W = W} {R′ = R′}
    {c = c} {d = d} {B = B} {B′ = B′} {pB = pB}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW target-rank
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

  source-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM)
  source-function-no = no•-ƛ source-body-no
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
  target-function-value = vW ⟨ c C.↦ d ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)
  target-W-no = cast-value-body-No• target-function-no

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
      (ƛ _) source-function-no
      target-function-value target-function-no
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

  function-final′ =
    subst
      (λ L′ → _ ∣ _ ∣ _ ∣ _ ∣ []
        ⊢ᴺ ƛ _ ⊑ L′
          ⦂ _ ⇒ _ ⊑ _ ⇒ _ ∶ _ ↦ _)
      (applyTerms-function-cast tail W c d)
      function-final

  target-W-value-final = applyTerms-preserves-Value tail vW
  target-W-no-final = applyTerms-preserves-No• tail target-W-no
  target-function-value-final =
    target-W-value-final ⟨
      applyCoercions tail c C.↦ applyCoercions tail d ⟩
  target-function-no-final =
    no•-⟨⟩ target-W-no-final
  target-argument-value-final = rightCatchupTargetValue catchup
  target-argument-no-final = rightCatchupTargetNoBullet catchup

  target-function-rank-final :
    suc (targetFunctionCastSpineRank target-W-value-final) ≡ n
  target-function-rank-final =
    trans
      (cong suc
        (target-function-cast-spine-rank-applyTerms tail vW))
      target-rank

  phase-two :
    WorldCoherentSourceOneStepIndexedResult
      {M = (ƛ N) · V}
      {M′ =
        (applyTerms tail W ⟨
          applyCoercions tail c C.↦ applyCoercions tail d ⟩) ·
        targetResult argument-result}
      {L = N [ V ]}
      {A = B}
      {B = applyTys tail B′}
      {χ = keep} {ρ = resultStore argument-result}
      (transportType argument-result pB)
  phase-two =
    value-terminal prefix-reflⁱ
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      okM
      (ok-·₂ target-function-value-final target-function-no-final
        (ok-no target-argument-no-final))
      function-final′
      (canonicalIndexedResults argument-indexed)
      vV target-W-value-final target-argument-value-final
      target-function-rank-final

  target-framed≡ :
    targetResult framed ≡
      (applyTerms tail W ⟨
        applyCoercions tail c C.↦ applyCoercions tail d ⟩) ·
      targetResult argument-result
  target-framed≡ =
    cong₂ _·_ (applyTerms-function-cast tail W c d) refl

  phase-two′ :
    WorldCoherentSourceOneStepIndexedResult
      {M = sourceResult framed} {M′ = targetResult framed}
      {L = N [ V ]}
      {A = resultSourceType framed}
      {B = resultTargetType framed}
      {χ = keep} {ρ = resultStore framed}
      (transportType argument-result pB)
  phase-two′ =
    subst
      (λ T →
        WorldCoherentSourceOneStepIndexedResult
          {M = sourceResult framed} {M′ = T}
          {L = N [ V ]}
          {A = resultSourceType framed}
          {B = resultTargetType framed}
          {χ = keep} {ρ = resultStore framed}
          (transportType argument-result pB))
      (sym target-framed≡)
      phase-two

  phase-two-indexed = sourceStepIndexedResult phase-two′
  phase-two-result = weakIndexedResult phase-two-indexed

  combined :
    WeakOneStepResult ρ⁺ ((ƛ N) · V)
      ((W ⟨ c C.↦ d ⟩) · R′) B B′ keep
  combined =
    sourceSilentResult composition framed refl refl phase-two-result

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition framed refl refl phase-two-result
      (sourceStepAssumptionMembershipUnique phase-two′)

  combined-type-eq =
    assumption-membership-unique→precision-index-unique
      combined-unique
      (subst
        (λ T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ applyTys (sourceChanges combined) B
            ⊑ T ⊣ resultRightCtx combined)
        (targetTypeResult combined)
        (subst
          (λ S → resultCtx combined ∣ resultLeftCtx combined
            ⊢ S ⊑ resultTargetType combined
              ⊣ resultRightCtx combined)
          (sourceTypeResult combined)
          (resultType combined)))
      (transportType combined pB)

  combined-transport =
    sourceSilentTransport composition framed refl refl phase-two-result
      framed-transport (weakIndexedTransport (sourceStepIndexedResult phase-two′))

  combined-coherence =
    sourceSilentTypeCoherence composition framed refl refl
      phase-two-result framed-coherence
      (weakIndexedTypeCoherence (sourceStepIndexedResult phase-two′))

  combined-indexed : WeakOneStepIndexedResult pB
  combined-indexed =
    weak-one-step-index-resultᵀ combined combined-type-eq
      combined-transport combined-coherence

  combined-lineage =
    sourceSilentStoreLineage composition framed refl refl
      phase-two-result framed-lineage
      (sourceStepStoreLineage phase-two′)

  combined-changes =
    sourceSilentChangesExact composition framed refl refl
      phase-two-result (sourceStepChangesExact phase-two′)

  combined-result =
    sourceSilentResultExact composition framed refl refl
      phase-two-result (sourceStepResultExact phase-two′)

  combined-world =
    sourceSilentWorldCoherent composition framed refl refl
      phase-two-result (sourceStepWorldCoherent phase-two′)

  combined-exclusive =
    sourceSilentSourceNameExclusive composition framed refl refl
      phase-two-result (sourceStepSourceNameExclusive phase-two′)


world-coherent-source-lambda-beta-target-function-cast-direct-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ
world-coherent-source-lambda-beta-target-function-cast-direct-proofᵀ
    right-catchup composition value-terminal
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW =
  world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ
    right-catchup composition value-at
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW refl
  where
  value-at :
    WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ
      (suc (targetFunctionCastSpineRank vW))
  value-at prefix₁ coherent₁ exclusive₁ unique₁ wfR₁ okM₁ okM′₁
      function-related₁ argument-related₁ vV₁ vW₁ vV′₁ rank-eq =
    value-terminal prefix₁ coherent₁ exclusive₁ unique₁ wfR₁
      okM₁ okM′₁ function-related₁ argument-related₁
      vV₁ vW₁ vV′₁
