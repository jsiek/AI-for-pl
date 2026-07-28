module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootProof
  where

-- File Charter:
--   * Implements the target natural-addition delta root by catching up the
--     source operands from left to right and then taking source delta.
--   * Uses exact constant inversion at each caught value and composes both
--     left-silent prefixes with their relational-store lineage.
--   * Stops immediately if either source operand catches up to blame.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     blame-root assumption, or compatibility wrapper.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  ( cong
  ; subst
  ; sym
  )
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; applyTerms
  ; applyTys
  ; δ-⊕
  ; pure-step
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; $
  ; blame
  ; no•-$
  ; no•-⊕
  ; ok-no
  ; ok-⊕₁
  ; ok-⊕₂
  ; _⊕[_]_
  )
open import Primitives using
  ( addℕ
  ; κℕ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; κ⊑κᵀ
  ; prefix-reflⁱ
  )
open import Types using
  ( TyCtx
  ; `ℕ
  ; ‵_
  )
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-one-step-index-resultᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; resultStore
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceResult
  ; sourceIsValueOrBlame
  ; targetIsUnchanged
  ; targetTailIsEmpty
  ; transportType
  ; transportNo•Terms
  ; weakIndexedResult
  ; weakIndexedTransport
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTys-ℕ
  ; applyTerms-const
  ; applyTerms-preserves-No•
  ; ⊕₁-↠
  ; ↠-trans
  )
open import proof.OneStep.NuImprecisionOneStepPrimitiveFrames using
  ( weak-one-step-⊕₁-indexed-frame-relatedᵀ
  ; weak-one-step-⊕₁-source-blame-frameᵀ
  ; weak-one-step-⊕₂-indexed-frame-relatedᵀ
  ; weak-one-step-⊕₂-source-blame-frameᵀ
  )
open import proof.OneStep.NuImprecisionOneStepPrimitiveLeaves using
  (related-nat-value-target-constantᵀ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootDef
  using (WorldCoherentRightOneStepPrimitiveDeltaRootᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  transport-idι-to-ℕ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    subst
      (λ T → Φ ∣ Δᴸ ⊢ ‵ `ℕ ⊑ T ⊣ Δᴿ)
      B≡ℕ
      (subst
        (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
        A≡ℕ p)
    ≡ idι
  transport-idι-to-ℕ refl refl idι = refl

  transport-term-to-ℕᵀ :
    ∀ {Φ Δᴸ Δᴿ A B ρ γ M M′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (A≡ℕ : A ≡ ‵ `ℕ) →
    (B≡ℕ : B ≡ ‵ `ℕ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
  transport-term-to-ℕᵀ {p = p} A≡ℕ B≡ℕ M⊑M′ =
    nu-term-imprecision-transport-typesᵀ
      A≡ℕ B≡ℕ (transport-idι-to-ℕ A≡ℕ B≡ℕ p) M⊑M′

  transport-nat-outcome :
    ∀ {Φ Δᴸ Δᴿ M N A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N} {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N} {A = A} {B = B}
      {χ = keep} {ρ = ρ} p
  transport-nat-outcome refl refl idι outcome = outcome


world-coherent-right-one-step-primitive-delta-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPrimitiveDeltaRootᵀ
world-coherent-right-one-step-primitive-delta-root-proofᵀ catchup =
  delta-root
  where
  delta-after-right-catchup :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M : Term} {m n : ℕ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK M →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = $ (κℕ m) ⊕[ addℕ ] M}
      {N′ = $ (κℕ (m + n))}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      with catchup coherent exclusive unique wfL
        okM ($ (κℕ n)) no•-$ M⊑n
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (weak-one-step-⊕₂-source-blame-frameᵀ
        ($ (κℕ m)) no•-$
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty
             (silentInvariant (catchupIndexedInvariant caught))
         | targetIsUnchanged
             (silentInvariant (catchupIndexedInvariant caught))
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl
      with related-nat-value-target-constantᵀ
        vW
        (transport-term-to-ℕᵀ
          (applyTys-ℕ
            (sourceChanges
              (weakIndexedResult (catchupIndexedResult caught))))
          refl
          (canonicalIndexedResults (catchupIndexedResult caught)))
  delta-after-right-catchup {m = m} {n = n}
      coherent exclusive unique wfL okM M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl | refl =
    world-coherent-left-silent-then-outcomeᵀ
      {p = idι {ι = `ℕ}}
      framed-silent framed-caught-lineage
      terminal-outcome-at-framed-source
    where
    caught-indexed = catchupIndexedResult caught
    caught-raw = weakIndexedResult caught-indexed
    transported-no-m =
      applyTerms-preserves-No• (sourceChanges caught-raw) no•-$
    framed-indexed =
      weak-one-step-⊕₂-indexed-frame-relatedᵀ
        ($ (κℕ m)) no•-$ ($ (κℕ m)) no•-$
        κ⊑κᵀ caught-indexed
    framed-raw = weakIndexedResult framed-indexed

    framed-silent : LeftSilentIndexedResult idι
    framed-silent =
      left-silent-indexed framed-indexed
        (left-silent-invariant refl refl)
        (ok-no (no•-⊕ transported-no-m no•-$))

    framed-caught-lineage =
      weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage)

    terminal-step = pure-step δ-⊕
    terminal-raw =
      weak-one-step-keep-source-catchupᵀ terminal-step κ⊑κᵀ
    terminal-indexed =
      weak-one-step-index-resultᵀ terminal-raw refl
        (weak-one-step-keep-source-catchup-transportᵀ
          terminal-step κ⊑κᵀ)
        (weak-one-step-keep-source-catchup-type-coherenceᵀ
          terminal-step κ⊑κᵀ)
    terminal-lineage =
      weak-step-store-lineage
        (resultStore terminal-raw)
        rel-store-embedding-reflⁱ prefix-reflⁱ
    terminal-outcome-nat =
      world-indexed-outcome-related
        terminal-indexed terminal-lineage
        final-coherent final-exclusive final-unique

    terminal-outcome-types :
      WorldCoherentWeakOneStepIndexedOutcome
        {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
        {N′ = $ (κℕ (m + n))}
        {χ = keep} {ρ = resultStore framed-raw}
        (transportType framed-raw idι)
    terminal-outcome-types =
      transport-nat-outcome
        (applyTys-ℕ (sourceChanges framed-raw))
        refl
        (transportType framed-raw idι)
        terminal-outcome-nat

    framed-source-eq :
      sourceResult framed-raw
        ≡ $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)
    framed-source-eq =
      cong (λ L → L ⊕[ addℕ ] $ (κℕ n))
        (applyTerms-const (sourceChanges caught-raw) (κℕ m))

    terminal-outcome-at-framed-source :
      WorldCoherentWeakOneStepIndexedOutcome
        {M = sourceResult framed-raw}
        {N′ = $ (κℕ (m + n))}
        {χ = keep} {ρ = resultStore framed-raw}
        (transportType framed-raw idι)
    terminal-outcome-at-framed-source =
      subst
        (λ S → WorldCoherentWeakOneStepIndexedOutcome
          {M = S} {N′ = $ (κℕ (m + n))}
          {A = applyTys (sourceChanges framed-raw) (‵ `ℕ)}
          {B = ‵ `ℕ}
          {χ = keep} {ρ = resultStore framed-raw}
          (transportType framed-raw (idι {ι = `ℕ})))
        (sym framed-source-eq)
        terminal-outcome-types

  delta-after-left-catchup :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M : Term} {m n : ℕ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK L →
    No• M →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ $ (κℕ m) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L ⊕[ addℕ ] M}
      {N′ = $ (κℕ (m + n))}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      with catchup coherent exclusive unique wfL
        okL ($ (κℕ m)) no•-$ L⊑m
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (weak-one-step-⊕₁-source-blame-frameᵀ noM
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty
             (silentInvariant (catchupIndexedInvariant caught))
         | targetIsUnchanged
             (silentInvariant (catchupIndexedInvariant caught))
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl
      with related-nat-value-target-constantᵀ
        vW
        (transport-term-to-ℕᵀ
          (applyTys-ℕ
            (sourceChanges
              (weakIndexedResult (catchupIndexedResult caught))))
          refl
          (canonicalIndexedResults (catchupIndexedResult caught)))
  delta-after-left-catchup {m = m} {n = n}
      coherent exclusive unique wfL okL noM L⊑m M⊑n
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | refl | refl =
    world-coherent-left-silent-then-outcomeᵀ
      {p = idι {ι = `ℕ}}
      framed-silent framed-caught-lineage right-outcome-types
    where
    caught-indexed = catchupIndexedResult caught
    caught-raw = weakIndexedResult caught-indexed
    transported-noM =
      applyTerms-preserves-No• (sourceChanges caught-raw) noM
    transported-M⊑n =
      transport-term-to-ℕᵀ
        (applyTys-ℕ (sourceChanges caught-raw))
        refl
        (transportNo•Terms (weakIndexedTransport caught-indexed)
          noM no•-$ M⊑n)

    framed-indexed =
      weak-one-step-⊕₁-indexed-frame-relatedᵀ
        noM no•-$ M⊑n caught-indexed
    framed-raw = weakIndexedResult framed-indexed

    framed-silent : LeftSilentIndexedResult idι
    framed-silent =
      left-silent-indexed framed-indexed
        (left-silent-invariant refl refl)
        (ok-no (no•-⊕ no•-$ transported-noM))

    framed-caught-lineage =
      weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage)

    right-outcome =
      delta-after-right-catchup
        final-coherent final-exclusive final-unique final-wfL
        (ok-no transported-noM) transported-M⊑n

    right-outcome-types =
      transport-nat-outcome
        (applyTys-ℕ (sourceChanges framed-raw))
        refl
        (transportType framed-raw idι)
        right-outcome

  delta-root :
    WorldCoherentRightOneStepPrimitiveDeltaRootᵀ
  delta-root coherent exclusive unique wfL
      (ok-no (no•-⊕ noL noM)) L⊑m M⊑n =
    delta-after-left-catchup
      coherent exclusive unique wfL
      (ok-no noL) noM L⊑m M⊑n
  delta-root coherent exclusive unique wfL
      (ok-⊕₁ okL noM) L⊑m M⊑n =
    delta-after-left-catchup
      coherent exclusive unique wfL
      okL noM L⊑m M⊑n
  delta-root coherent exclusive unique wfL
      (ok-⊕₂ vL noL okM) L⊑m M⊑n
      with related-nat-value-target-constantᵀ vL L⊑m
  delta-root coherent exclusive unique wfL
      (ok-⊕₂ vL noL okM) L⊑m M⊑n | refl =
    delta-after-right-catchup
      coherent exclusive unique wfL okM M⊑n
