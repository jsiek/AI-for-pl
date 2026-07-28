module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedWideningProof
  where

-- File Charter:
--   * Proves the exact live paired-widening value terminal for right-leading
--     function-cast beta.
--   * Handles hereditary function compatibility, excludes a target-active
--     function coercion, and distributes the inert-target bridge.
--   * Contains no reveal/conceal conversion, quotient closure, retired
--     paired-cast carrier, dispatcher, postulate, hole, or catch-all.

import CastImprecisionShape as CastShape
import Coercions as C
import NarrowWiden as NW
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; comp-↦-↦
  ; quotient-boundary-square
  ; source-perm-refl
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (β-↦; keep; pure-step)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; no•-⟨⟩; _·_; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; compatible-functionᴿ
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; _⇒_)
open import
  proof.Core.Properties.TypePreservation
  using (seal★-weaken)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; value-runtime-No•)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
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


right-step-application-function-cast-beta-paired-widening-values-proofᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {A₀ A₀′ A A′ B₀ B₀′ B B′ : Ty}
    {pA₀ : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {pB₀ : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s s′ r : ImprecisionShape} {μ μ′} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᵇ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
    ⊢ c C.↦ d ∶ A₀ ⇒ B₀ ⊑ A ⇒ B →
  CastShape.widening CastShape.⊢ᶜ
    c C.↦ d ⦂ s →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ e C.↦ f ∶ A₀′ ⇒ B₀′ ⊑ A′ ⇒ B′ →
  CastShape.widening CastShape.⊢ᶜ
    e C.↦ f ⦂ s′ →
  s ； ⌊ pA ↦ pB ⌋ ≋ r →
  ⌊ pA₀ ↦ pB₀ ⌋ ； s′ ≋ r →
  ReductionClosedPairedWideningCompatible Φ Δᴸ Δᴿ
    (c C.↦ d) (e C.↦ f)
    (pA₀ ↦ pB₀) (pA ↦ pB) s s′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⊑ V′
      ⦂ A₀ ⇒ B₀ ⊑ A₀′ ⇒ B₀′ ∶ pA₀ ↦ pB₀ →
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
right-step-application-function-cast-beta-paired-widening-values-proofᵀ
    function-compatible
    relation-prefix coherent exclusive unique wfL okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    source-comp target-comp
    (compatible-functionᴿ compatible)
    inner argument-related vV vM vV′ vW′ =
  source-result-outcome
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vM)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  seal★′⁺ = seal★-weaken right-incl seal★′
  c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
  source-widening⁺ =
    C.cast-fun (proj₁ c⊒⁺) (proj₁ d⊑⁺) ,
    NW.cross (cⁿ NW.↦ dʷ)
  e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
  f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
  target-widening⁺ =
    C.cast-fun (proj₁ e⊒⁺) (proj₁ f⊑⁺) ,
    NW.cross (eⁿ NW.↦ fʷ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-V-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-V-no inner
  final-related =
    function-compatible mode seal★⁺ source-widening⁺
      (CastShape.shape-fun c-shape d-shape)
      mode′ seal★′⁺ target-widening⁺
      (CastShape.shape-fun e-shape f-shape)
      (quotient-boundary-square
        source-perm-refl source-comp
        source-perm-refl target-comp)
      compatible inner⁺ argument-related
right-step-application-function-cast-beta-paired-widening-values-proofᵀ
    function-compatible
    relation-prefix coherent exclusive unique wfL okM okM′
    mode seal★ source-widening source-shape
    mode′ seal★′ target-widening target-shape
    source-comp target-comp
    (compatible-target-activeᴿ inert target-active)
    inner argument-related vV vM vV′ vW′ =
  ⊥-elim (target-active (_ C.↦ _))
right-step-application-function-cast-beta-paired-widening-values-proofᵀ
    function-compatible
    {pA₀ = pA₀} {pB₀ = pB₀} {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    source-comp target-comp
    (compatible-target-inert-bridgeᴿ bridge)
    inner argument-related vV vM vV′ vW′
    with bridge (_ C.↦ _)
right-step-application-function-cast-beta-paired-widening-values-proofᵀ
    function-compatible
    {pA₀ = pA₀} {pB₀ = pB₀} {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique wfL okM okM′
    mode seal★
    (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
    (CastShape.shape-fun c-shape d-shape)
    mode′ seal★′
    (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
    (CastShape.shape-fun e-shape f-shape)
    source-comp target-comp
    (compatible-target-inert-bridgeᴿ bridge)
    inner argument-related vV vM vV′ vW′
    | (pA-bridge ↦ pB-bridge)
        , (comp-↦-↦ c-comp d-comp)
        , (comp-↦-↦ e-comp f-comp) =
  source-result-outcome
    (world-coherent-source-keep-relationᵀ
      coherent exclusive unique final-related
      (pure-step (β-↦ vV vM)))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  seal★′⁺ = seal★-weaken right-incl seal★′
  c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
  e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
  f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (vV′ ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM′)
  target-V-no = cast-value-body-No• target-function-no
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-V-no inner
  target-argument-cast =
    ⊑cast⊒ᵀ mode′ seal★′⁺ e⊒⁺ argument-related pA-bridge
      e-shape e-comp
  argument-casts =
    cast⊒⊑ᵀ mode seal★⁺ c⊒⁺ target-argument-cast pA₀
      c-shape c-comp
  application-related = ·⊑·ᵀ inner⁺ argument-casts
  source-result-cast =
    cast⊑⊑ᵀ mode seal★⁺ d⊑⁺ application-related pB-bridge
      d-shape d-comp
  final-related =
    ⊑cast⊑ᵀ mode′ seal★′⁺ f⊑⁺ source-result-cast pB
      f-shape f-comp
