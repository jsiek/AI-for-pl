module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedValueRootProof
  where

-- File Charter:
--   * Assembles the complete `conv⊑convᵀ` target value-root boundary by
--     deciding whether the source cast is inert.
--   * Dispatches source-inert pairs to whole-source value catch-up and keeps
--     source-active pairs behind the exact synchronized active-value cell.
--   * Contains no quotient case, synchronized active-root implementation,
--     recursive dispatcher, postulate, hole, or permissive option.

open import Coercions using (Coercion)
open import Data.List using ([])
open import Data.Unit using (⊤)
open import Relation.Nullary using (yes; no)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.CoercionProperties using (inert-dec)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootLemma
  using (world-coherent-right-one-step-paired-source-active-value-rootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootLemma
  using (world-coherent-right-one-step-paired-source-inert-value-rootᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-value-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ N′ : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion}
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
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  V′ ⟨ c′ ⟩ —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′}
    {χ = keep} {ρ = ρ} q
world-coherent-right-one-step-paired-value-root-proofᵀ
    left-catchup right-catchup runtime-transport synchronize
    coherent exclusive unique wfL wfR ok-source ok-target vV′
    paired M⊑V′ target-root
    with inert-dec _
world-coherent-right-one-step-paired-value-root-proofᵀ
    left-catchup right-catchup runtime-transport synchronize
    coherent exclusive unique wfL wfR ok-source ok-target vV′
    paired M⊑V′ target-root
    | yes inert =
  world-coherent-right-one-step-paired-source-inert-value-rootᵀ
    left-catchup right-catchup runtime-transport
    coherent exclusive unique wfL wfR ok-source ok-target vV′ inert
    paired M⊑V′ target-root
world-coherent-right-one-step-paired-value-root-proofᵀ
    left-catchup right-catchup runtime-transport synchronize
    coherent exclusive unique wfL wfR ok-source ok-target vV′
    paired M⊑V′ target-root
    | no noninert =
  world-coherent-right-one-step-paired-source-active-value-rootᵀ
    left-catchup synchronize
    coherent exclusive unique wfL wfR ok-source ok-target vV′ noninert
    paired M⊑V′ target-root
