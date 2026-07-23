module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectProof
  where

-- File Charter:
--   * Proves direct ordinary lambda-beta scheduling by target-function shape.
--   * Catches up a non-value target function, transports the untouched
--     argument, then dispatches to lambda or function-cast terminals.
--   * Contains no terminal implementation, postulate, hole, or option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)

open import ImprecisionWf using (_↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTerms; keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-·
  ; no•-ƛ
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; ƛ_
  ; _·_
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (forget; ⊢·)
open import Types using (Ty; _⇒_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.NuImprecisionSimulationCore using
  ( weak-indexed-arrow-resultᵀ
  ; weak-one-step-·₁-frameᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalArrowResults
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; weakArrowResult
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-step-transport
  ; weak-step-type-coherence
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
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  ; worldRightCatchupTargetStoreWf
  )
open import proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectCasesDef
  using
  ( WorldCoherentSourceLambdaBetaDirectCases
  ; sourceLambdaBetaTargetFunctionCastDirectCase
  ; sourceLambdaBetaTargetLambdaDirectCase
  )
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionDef
  using (WorldCoherentSourceSilentCompositionᵀ)
open import proof.NuPreservation using
  (runtime-·₁; runtime-·₂; value-runtime-No•)
open import proof.NuProgress using
  (canonical-⇒; fv-ƛ; fv-↦)
open import proof.ReductionProperties using
  (applyTerms-preserves-No•)
open import proof.TypePreservation using (term-weaken)


private
  lambda-runtime-No• :
    ∀ {N} →
    RuntimeOK (ƛ N) →
    No• (ƛ N)
  lambda-runtime-No• (ok-no noN) = noN


finish-source-lambda-function-catchupᵀ :
  WorldCoherentSourceLambdaBetaDirectCases →
  WorldCoherentSourceSilentCompositionᵀ →
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N V L′ R′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  RuntimeOK ((ƛ N) · V) →
  Value V →
  No• V →
  No• R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentRightValueCatchupIndexedResult
    {V = ƛ N} {M′ = L′} {ρ = ρ} (pA ↦ pB) →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = L′ · R′} {L = N [ V ]}
    {A = B} {B = B′} {χ = keep} {ρ = ρ} pB
finish-source-lambda-function-catchupᵀ
    cases compose okM vV noV noR argument-related caught
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult caught
finish-source-lambda-function-catchupᵀ
    cases compose okM vV noV noR argument-related caught
    | refl | refl
    with canonical-⇒ target-function-value
      (forget (nu-term-imprecision-target-typing function-final))
  where
  catchup = worldRightCatchupResult caught
  function-indexed = rightCatchupIndexedResult catchup
  function-result = weakIndexedResult function-indexed
  function-arrow =
    weak-indexed-arrow-resultᵀ function-indexed
  function-final = canonicalArrowResults function-arrow
  target-function-value = rightCatchupTargetValue catchup
finish-source-lambda-function-catchupᵀ
    cases compose okM vV noV noR argument-related caught
    | refl | refl | fv-ƛ refl =
  compose framed refl refl framed-transport framed-coherence
    framed-lineage phase-two
  where
  catchup = worldRightCatchupResult caught
  function-indexed = rightCatchupIndexedResult catchup
  function-result = weakIndexedResult function-indexed
  function-arrow =
    weak-indexed-arrow-resultᵀ function-indexed
  function-final = canonicalArrowResults function-arrow
  target-function-value = rightCatchupTargetValue catchup
  target-function-no = rightCatchupTargetNoBullet catchup
  target-argument-no =
    applyTerms-preserves-No•
      (targetTailChanges function-result) noR
  argument-final =
    transportNo•Terms (weakIndexedTransport (rightCatchupIndexedResult catchup))
      noV noR argument-related
  framed =
    weak-one-step-·₁-frameᵀ noV noR function-result
      function-final argument-final
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
  phase-two =
    sourceLambdaBetaTargetLambdaDirectCase cases
      prefix-reflⁱ
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      okM
      (ok-·₂ target-function-value target-function-no
        (ok-no target-argument-no))
      function-final argument-final vV
finish-source-lambda-function-catchupᵀ
    cases compose okM vV noV noR argument-related caught
    | refl | refl | fv-↦ vW refl =
  compose framed refl refl framed-transport framed-coherence
    framed-lineage phase-two
  where
  catchup = worldRightCatchupResult caught
  function-indexed = rightCatchupIndexedResult catchup
  function-result = weakIndexedResult function-indexed
  function-arrow =
    weak-indexed-arrow-resultᵀ function-indexed
  function-final = canonicalArrowResults function-arrow
  target-function-value = rightCatchupTargetValue catchup
  target-function-no = rightCatchupTargetNoBullet catchup
  target-argument-no =
    applyTerms-preserves-No•
      (targetTailChanges function-result) noR
  argument-final =
    transportNo•Terms (weakIndexedTransport (rightCatchupIndexedResult catchup))
      noV noR argument-related
  framed =
    weak-one-step-·₁-frameᵀ noV noR function-result
      function-final argument-final
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
  phase-two =
    sourceLambdaBetaTargetFunctionCastDirectCase cases
      prefix-reflⁱ
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      okM
      (ok-·₂ target-function-value target-function-no
        (ok-no target-argument-no))
      function-final argument-final vV vW


catch-source-lambda-function-then-finishᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceLambdaBetaDirectCases →
  WorldCoherentSourceSilentCompositionᵀ →
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V L′ R′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK L′ →
  Value V →
  No• V →
  No• R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ƛ N ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = L′ · R′} {L = N [ V ]}
    {A = B} {B = B′} {χ = keep} {ρ = ρ⁺} pB
catch-source-lambda-function-then-finishᵀ
    right-catchup cases compose prefix coherent exclusive unique wfR
    okM okL′ vV noV noR function-related argument-related =
  finish-source-lambda-function-catchupᵀ
    cases compose okM vV noV target-argument-no
    argument-related⁺
    (right-catchup prefix coherent exclusive unique wfR okL′
      (ƛ _) source-function-no function-related)
  where
  source-function-no = lambda-runtime-No• (runtime-·₁ okM)
  source-argument⊢⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix) noV
      (nu-term-imprecision-source-typing argument-related)
  target-argument⊢⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix) noR
      (nu-term-imprecision-target-typing argument-related)
  argument-related⁺ =
    allocation-prefixᵀ prefix argument-related
      source-argument⊢⁺ target-argument⊢⁺
  target-argument-no = noR


world-coherent-source-lambda-beta-direct-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSilentCompositionᵀ →
  WorldCoherentSourceLambdaBetaDirectCases →
  WorldCoherentSourceLambdaBetaDirectᵀ
world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup compose cases
    prefix coherent exclusive unique wfL wfR okM
    (ok-no (no•-· noL′ noR′)) source⊢
    target⊢ function-related argument-related vV =
  catch-source-lambda-function-then-finishᵀ
    right-catchup cases compose prefix coherent exclusive unique wfR
    okM (ok-no noL′) vV source-argument-no noR′
    function-related argument-related
  where
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup compose cases
    prefix coherent exclusive unique wfL wfR okM
    (ok-·₁ okL′ noR′) source⊢
    target⊢ function-related argument-related vV =
  catch-source-lambda-function-then-finishᵀ
    right-catchup cases compose prefix coherent exclusive unique wfR
    okM okL′ vV source-argument-no noR′
    function-related argument-related
  where
  source-argument-no =
    value-runtime-No• vV (runtime-·₂ (ƛ _) okM)
world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup compose cases
    prefix coherent exclusive unique wfL wfR okM
    okM′@(ok-·₂ vL′ noL′ okR′) source⊢
    (⊢· target-function⊢ target-argument⊢)
    function-related argument-related vV
    with canonical-⇒ vL′ (forget target-function⊢)
world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup compose cases
    prefix coherent exclusive unique wfL wfR okM
    okM′@(ok-·₂ vL′ noL′ okR′) source⊢
    (⊢· target-function⊢ target-argument⊢)
    function-related argument-related vV | fv-ƛ refl =
  sourceLambdaBetaTargetLambdaDirectCase cases
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV
world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup compose cases
    prefix coherent exclusive unique wfL wfR okM
    okM′@(ok-·₂ vL′ noL′ okR′) source⊢
    (⊢· target-function⊢ target-argument⊢)
    function-related argument-related vV | fv-↦ vW refl =
  sourceLambdaBetaTargetFunctionCastDirectCase cases
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW
