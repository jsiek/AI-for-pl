module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedConversionProof
  where

-- File Charter:
--   * Proves the exact paired-reveal and paired-conceal value terminals for
--     right-leading function-cast beta.
--   * Rebuilds paired argument and result conversions after store-prefix
--     weakening, then takes exactly the source function-beta step.
--   * Contains no widening, quotient closure, retired paired-cast carrier,
--     dispatcher, postulate, hole, or compatibility wrapper.

import Coercions as C
import Conversion as CV
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_; replace-paired-function)
open import Data.List using ([])
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (β-↦; keep; pure-step)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; no•-⟨⟩; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  (Ty; TyCtx; _⇒_)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; value-runtime-No•)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using (store-corresponds-prefix-proofᵀ)
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using (quotiented-store-prefix-no-bullet-proofᵀ)
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


right-step-application-function-cast-beta-paired-reveal-values-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {C C′ A A′ B B′ X X′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {α β pX μ μ′} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  StoreCorresponds ρᵇ α X β X′ pX →
  CV.RevealConversion μ Δᴸ (leftStoreⁱ ρᵇ)
    α X (c C.↦ d) C (A ⇒ B) →
  CV.RevealConversion μ′ Δᴿ (rightStoreⁱ ρᵇ)
    β X′ (e C.↦ f) C′ (A′ ⇒ B′) →
  pC [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ (pA ↦ pB) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
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
right-step-application-function-cast-beta-paired-reveal-values-proofᵀ
    {pC = pA₀ ↦ pB₀}
    relation-prefix coherent exclusive unique wfL okM okM′
    corresponds
    (CV.reveal-fun c↓ d↑)
    (CV.reveal-fun e↓ f↑)
    (replace-paired-function c-replace d-replace)
    inner argument-related vV vM vV′ vW′ =
  source-result-outcome
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vM)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  corresponds⁺ =
    store-corresponds-prefix-proofᵀ relation-prefix corresponds
  c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
  d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
  e↓⁺ = CV.weaken-conceal-conversion right-incl e↓
  f↑⁺ = CV.weaken-reveal-conversion right-incl f↑
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-V-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-V-no inner
  argument-cast =
    paired-concealᵀ corresponds⁺ c↓⁺ e↓⁺ c-replace
      argument-related
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    paired-revealᵀ corresponds⁺ d↑⁺ f↑⁺ d-replace
      application-related


right-step-application-function-cast-beta-paired-conceal-values-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {C C′ A A′ B B′ X X′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {α β pX μ μ′} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  StoreCorresponds ρᵇ α X β X′ pX →
  CV.ConcealConversion μ Δᴸ (leftStoreⁱ ρᵇ)
    α X (c C.↦ d) C (A ⇒ B) →
  CV.ConcealConversion μ′ Δᴿ (rightStoreⁱ ρᵇ)
    β X′ (e C.↦ f) C′ (A′ ⇒ B′) →
  (pA ↦ pB) [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ pC →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
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
right-step-application-function-cast-beta-paired-conceal-values-proofᵀ
    {pC = pA₀ ↦ pB₀}
    relation-prefix coherent exclusive unique wfL okM okM′
    corresponds
    (CV.conceal-fun c↑ d↓)
    (CV.conceal-fun e↑ f↓)
    (replace-paired-function c-replace d-replace)
    inner argument-related vV vM vV′ vW′ =
  source-result-outcome
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vM)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  corresponds⁺ =
    store-corresponds-prefix-proofᵀ relation-prefix corresponds
  c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
  d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
  e↑⁺ = CV.weaken-reveal-conversion right-incl e↑
  f↓⁺ = CV.weaken-conceal-conversion right-incl f↓
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-V-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-V-no inner
  argument-cast =
    paired-revealᵀ corresponds⁺ c↑⁺ e↑⁺ c-replace
      argument-related
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    paired-concealᵀ corresponds⁺ d↓⁺ f↓⁺ d-replace
      application-related
