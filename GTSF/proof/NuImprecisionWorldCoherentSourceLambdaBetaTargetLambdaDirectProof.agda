module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectProof
  where

-- File Charter:
--   * Proves direct lambda/lambda scheduling by catching up the target
--     argument and composing that silent trace with synchronized beta.
--   * Uses precision-index uniqueness only to reindex the composed result.
--   * Contains no function-cast case, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym)

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
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
  ; ok-no
  ; ƛ_
  ; _·_
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; ƛ⊑ƛᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (⊢ƛ; ⊢·)
open import Types using (Ty; _⇒_)
open import proof.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.NuImprecisionSimulationCore using
  ( weak-one-step-index-resultᵀ
  ; weak-one-step-·₂-indexed-frameᵀ
  ; weak-result-transport-arrow-termsᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
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
open import proof.NuImprecisionSourceSilentCompositionDef using
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
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  )
open import proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectDef
  using (WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
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
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)
open import proof.NuPreservation using
  (runtime-·₁; runtime-·₂; value-runtime-No•)
open import proof.ReductionProperties using
  (applyTerms-preserves-No•)
open import proof.TypePreservation using (term-weaken)


private
  lambda-runtime-body-No• :
    ∀ {N} →
    RuntimeOK (ƛ N) →
    No• N
  lambda-runtime-body-No• (ok-no (no•-ƛ noN)) = noN

  applyTerms-ƛ :
    ∀ χs N →
    applyTerms χs (ƛ N) ≡ ƛ applyTerms χs N
  applyTerms-ƛ [] N = refl
  applyTerms-ƛ (keep ∷ χs) N = applyTerms-ƛ χs N
  applyTerms-ƛ (bind A ∷ χs) N = applyTerms-ƛ χs _


related-lambda-bodiesᵀ :
  ∀ {Φ Δᴸ Δᴿ N N′ A A′ B B′ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ ƛ N ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
related-lambda-bodiesᵀ (ƛ⊑ƛᵀ hA hA′ body) = body
related-lambda-bodiesᵀ
    (allocation-prefixᵀ prefix inner
      (⊢ƛ hA body⊢) (⊢ƛ hA′ body′⊢)) =
  allocation-prefixᵀ prefix (related-lambda-bodiesᵀ inner)
    body⊢ body′⊢


world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  SourceSilentComposition →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ
world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
    right-catchup composition synchronized
    {N = N} {N′ = N′} {V = V} {B = B} {B′ = B′}
    {pB = pB}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV
    with right-catchup prefix coherent exclusive unique wfR
      (runtime-·₂ (ƛ _) okM′) vV source-argument-no
      argument-related
  where
  source-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM)
  source-function-no = no•-ƛ source-body-no
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
    right-catchup composition synchronized
    {N = N} {N′ = N′} {V = V} {B = B} {B′ = B′}
    {pB = pB}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV
    | caught
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult caught
world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
    right-catchup composition synchronized
    {ρ⁺ = ρ⁺} {N = N} {N′ = N′} {V = V} {R′ = R′}
    {B = B} {B′ = B′} {pB = pB}
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV
    | caught | refl | refl =
  world-coherent-source-one-step-indexed
    combined-indexed
    combined-lineage combined-changes combined-result combined-world
    combined-exclusive combined-unique
  where
  catchup = worldRightCatchupResult caught
  argument-indexed = rightCatchupIndexedResult catchup
  argument-result = weakIndexedResult argument-indexed

  source-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM)
  source-function-no = no•-ƛ source-body-no
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
  target-body-no =
    lambda-runtime-body-No• (runtime-·₁ okM′)
  target-function-no = no•-ƛ target-body-no

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
      (ƛ _) source-function-no (ƛ _) target-function-no
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
      (applyTerms-ƛ (targetTailChanges argument-result) _)
      function-final

  body-final = related-lambda-bodiesᵀ function-final′

  target-body-final-no =
    applyTerms-preserves-No•
      (targetTailChanges argument-result) target-body-no

  phase-two :
    WorldCoherentSourceOneStepIndexedResult
      {M = (ƛ N) · V}
      {M′ = (ƛ applyTerms (targetTailChanges argument-result) N′) ·
        targetResult argument-result}
      {L = N [ V ]}
      {A = B}
      {B = applyTys (targetTailChanges argument-result) B′}
      {χ = keep} {ρ = resultStore argument-result}
      (transportType argument-result pB)
  phase-two =
    synchronized
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      vV source-argument-no
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      source-body-no target-body-final-no
      body-final
      (canonicalIndexedResults argument-indexed)

  target-framed≡ :
    targetResult framed ≡
      (ƛ applyTerms (targetTailChanges argument-result) N′) ·
        targetResult argument-result
  target-framed≡ =
    cong₂ _·_
      (applyTerms-ƛ (targetTailChanges argument-result) N′)
      refl

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
    WeakOneStepResult ρ⁺ ((ƛ N) · V) ((ƛ N′) · R′) B B′ keep
  combined =
    sourceSilentResult composition framed refl refl phase-two-result

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition framed refl refl phase-two-result
      (sourceStepAssumptionMembershipUnique phase-two′)

  combined-type-eq :
    subst
      (λ T → resultCtx combined ∣ resultLeftCtx combined
        ⊢ applyTys (sourceChanges combined) B
          ⊑ T ⊣ resultRightCtx combined)
      (targetTypeResult combined)
      (subst
        (λ S → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ resultTargetType combined
            ⊣ resultRightCtx combined)
        (sourceTypeResult combined)
        (resultType combined))
    ≡ transportType combined pB
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
    sourceSilentTypeCoherence composition framed refl refl phase-two-result
      framed-coherence (weakIndexedTypeCoherence (sourceStepIndexedResult phase-two′))

  combined-indexed : WeakOneStepIndexedResult pB
  combined-indexed =
    weak-one-step-index-resultᵀ combined combined-type-eq
      combined-transport combined-coherence

  combined-lineage =
    sourceSilentStoreLineage composition framed refl refl phase-two-result
      framed-lineage (sourceStepStoreLineage phase-two′)

  combined-changes =
    sourceSilentChangesExact composition framed refl refl phase-two-result
      (sourceStepChangesExact phase-two′)

  combined-result =
    sourceSilentResultExact composition framed refl refl phase-two-result
      (sourceStepResultExact phase-two′)

  combined-world =
    sourceSilentWorldCoherent composition framed refl refl phase-two-result
      (sourceStepWorldCoherent phase-two′)

  combined-exclusive =
    sourceSilentSourceNameExclusive
      composition framed refl refl phase-two-result
      (sourceStepSourceNameExclusive phase-two′)
