module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectProof
  where

-- File Charter:
--   * Proves direct source function-cast beta scheduling by first catching up
--     an arbitrary target function to a value.
--   * Frames that function trace around the untouched argument, then delegates
--     all remaining work to the target-value boundary.
--   * Contains no coercion algebra, target-value implementation, postulate,
--     hole, or permissive option.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)

open import ImprecisionWf using (_↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-·
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; _⇒_)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  ; rightCatchupTransport
  ; rightCatchupTypeCoherence
  )
open import proof.NuImprecisionSimulationCore using
  ( weak-indexed-arrow-resultᵀ
  ; weak-one-step-·₁-frameᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalArrowResults
  ; targetTailChanges
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; weakIndexedResult
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
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueDef
  using (WorldCoherentSourceFunctionCastBetaTargetValueᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionDef
  using (WorldCoherentSourceSilentCompositionᵀ)
open import proof.NuPreservation using
  (runtime-·₁; runtime-·₂; value-runtime-No•)
open import proof.ReductionProperties using
  (applyTerms-preserves-No•)
open import proof.TypePreservation using (term-weaken)


finish-source-function-cast-function-catchupᵀ :
  WorldCoherentSourceFunctionCastBetaTargetValueᵀ →
  WorldCoherentSourceSilentCompositionᵀ →
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  Value V →
  Value W →
  No• W →
  No• R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V ⟨ c C.↦ d ⟩} {M′ = L′} {ρ = ρ} (pA ↦ pB) →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {A = B} {B = B′} {χ = keep} {ρ = ρ} pB
finish-source-function-cast-function-catchupᵀ
    target-value compose okM vV vW noW noR argument-related caught
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult caught
finish-source-function-cast-function-catchupᵀ
    target-value compose okM vV vW noW noR argument-related caught
    | refl | refl =
  compose framed refl refl framed-transport framed-coherence
    framed-lineage phase-two
  where
  catchup = worldRightCatchupResult caught
  function-indexed = rightCatchupIndexedResult catchup
  function-result = weakIndexedResult function-indexed
  function-arrow =
    weak-indexed-arrow-resultᵀ function-indexed
      (rightCatchupTypeCoherence catchup)
  function-final = canonicalArrowResults function-arrow
  target-function-value = rightCatchupTargetValue catchup
  target-function-no = rightCatchupTargetNoBullet catchup
  target-argument-no =
    applyTerms-preserves-No•
      (targetTailChanges function-result) noR
  argument-final =
    transportNo•Terms (rightCatchupTransport catchup)
      noW noR argument-related
  framed =
    weak-one-step-·₁-frameᵀ noW noR function-result
      function-final argument-final
  framed-transport =
    weak-step-transport
      (transportNo•Terms (rightCatchupTransport catchup))
  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent (rightCatchupTypeCoherence catchup))
      (transportAllCoherent (rightCatchupTypeCoherence catchup))
  framed-lineage : WeakOneStepStoreLineage framed
  framed-lineage =
    weak-step-store-lineage
      (lineageStore caught-lineage)
      (lineageEmbedding caught-lineage)
      (lineagePrefix caught-lineage)
    where
    caught-lineage = worldRightCatchupStoreLineage caught
  phase-two =
    target-value
      prefix-reflⁱ
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      okM
      (ok-·₂ target-function-value target-function-no
        (ok-no target-argument-no))
      function-final argument-final vV vW target-function-value


catch-source-function-cast-function-then-finishᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaTargetValueᵀ →
  WorldCoherentSourceSilentCompositionᵀ →
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK L′ →
  Value V →
  Value W →
  No• R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {A = B} {B = B′} {χ = keep} {ρ = ρ⁺} pB
catch-source-function-cast-function-then-finishᵀ
    right-catchup target-value compose {c = c} {d = d}
    prefix coherent exclusive unique wfR
    okM okL′ vV vW noR function-related argument-related =
  finish-source-function-cast-function-catchupᵀ
    target-value compose okM vV vW source-argument-no target-argument-no
    argument-related⁺
    (right-catchup prefix coherent exclusive unique wfR okL′
      source-function-value source-function-no function-related)
  where
  source-function-value = vV ⟨ c C.↦ d ⟩
  source-function-no =
    value-runtime-No• source-function-value (runtime-·₁ okM)
  source-argument-no =
    value-runtime-No• vW (runtime-·₂ source-function-value okM)
  source-argument⊢⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      source-argument-no
      (nu-term-imprecision-source-typing argument-related)
  target-argument⊢⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noR
      (nu-term-imprecision-target-typing argument-related)
  argument-related⁺ =
    allocation-prefixᵀ prefix argument-related
      source-argument⊢⁺ target-argument⊢⁺
  target-argument-no = noR


world-coherent-source-function-cast-beta-direct-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSilentCompositionᵀ →
  WorldCoherentSourceFunctionCastBetaTargetValueᵀ →
  WorldCoherentSourceFunctionCastBetaDirectᵀ
world-coherent-source-function-cast-beta-direct-proofᵀ
    right-catchup compose target-value
    prefix coherent exclusive unique wfL wfR okM
    (ok-no (no•-· noL′ noR′)) source⊢ target⊢
    function-related argument-related vV vW =
  catch-source-function-cast-function-then-finishᵀ
    right-catchup target-value compose prefix coherent exclusive unique wfR
    okM (ok-no noL′) vV vW noR′ function-related argument-related
world-coherent-source-function-cast-beta-direct-proofᵀ
    right-catchup compose target-value
    prefix coherent exclusive unique wfL wfR okM
    (ok-·₁ okL′ noR′) source⊢ target⊢
    function-related argument-related vV vW =
  catch-source-function-cast-function-then-finishᵀ
    right-catchup target-value compose prefix coherent exclusive unique wfR
    okM okL′ vV vW noR′ function-related argument-related
world-coherent-source-function-cast-beta-direct-proofᵀ
    right-catchup compose target-value
    prefix coherent exclusive unique wfL wfR okM
    okM′@(ok-·₂ vL′ noL′ okR′) source⊢ target⊢
    function-related argument-related vV vW =
  target-value prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vL′
