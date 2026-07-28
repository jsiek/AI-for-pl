module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientProof
  where

-- File Charter:
--   * Proves the quotient-closing paired function-cast beta terminal.
--   * Preserves quotient narrowing, widening-pair, shape-square, and
--     reduction-closed compatibility evidence under the store prefix.
--   * Contains no ordinary paired conversion/widening case, retired
--     paired-cast carrier, dispatcher, postulate, hole, or wrapper.

import CastImprecisionShape as CastShape
import Coercions as C
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (β-↦; keep; pure-step)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; no•-⟨⟩; _·_; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using
  (Ty; TyCtx; _⇒_)
open import proof.DGG.Core.NuPreservation using
  (value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-·₁)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using (quotient-widening-pair-prefix-proofᵀ)
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using (quotiented-store-prefix-no-bulletᵖ-proofᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceKeepRelationLemma
  using (world-coherent-source-keep-relationᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepIndexedResult
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  )


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV

  source-result-outcome :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ L : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherentSourceOneStepIndexedResult
      {M = M} {M′ = M′} {L = L}
      {χ = keep} {ρ = ρ} p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p
  source-result-outcome complete =
    world-indexed-outcome-related
      (sourceStepIndexedResult complete)
      (sourceStepStoreLineage complete)
      (sourceStepWorldCoherent complete)
      (sourceStepSourceNameExclusive complete)
      (sourceStepAssumptionMembershipUnique complete)


right-step-application-function-cast-beta-paired-quotient-values-proofᵀ :
  SourceFunctionCastBetaPairedQuotientRelationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {D D′ A A′ B B′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s s′ : ImprecisionShape} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺᵖ V ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ
    (c C.↦ d) (e C.↦ f)
    D D′ (A ⇒ B) (A′ ⇒ B′) →
  CastShape.widening CastShape.⊢ᶜ
    (c C.↦ d) ⦂ s →
  CastShape.widening CastShape.⊢ᶜ
    (e C.↦ f) ⦂ s′ →
  s ；⌊ pA ↦ pB ⌋≋ᵖ qD ； s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ (c C.↦ d) (e C.↦ f)
    qD (pA ↦ pB) s s′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value M →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ c C.↦ d ⟩) · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB
right-step-application-function-cast-beta-paired-quotient-values-proofᵀ
    quotient relation-prefix coherent exclusive unique wfL okM okM′
    inner widening source-shape target-shape square compatible
    argument-related vV vM vV′ vW′ =
  source-result-outcome
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vM)))
  where
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-V-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bulletᵖ-proofᵀ
      relation-prefix source-V-no target-V-no inner
  widening⁺ =
    quotient-widening-pair-prefix-proofᵀ relation-prefix widening
  final-related =
    quotient inner⁺ widening⁺ source-shape target-shape square
      compatible argument-related
