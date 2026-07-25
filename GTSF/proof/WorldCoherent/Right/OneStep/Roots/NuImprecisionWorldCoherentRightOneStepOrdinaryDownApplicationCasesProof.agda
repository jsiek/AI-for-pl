module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationCasesProof
  where

-- File Charter:
--   * Exhausts target application steps for the
--     `ordinary-down-applicationᵖᵀ` QTIP constructor beneath `up⊑upᵀ`.
--   * Dispatches function and argument frames to their quotient-aware
--     schedulers, isolates the beta roots, and proves left blame directly.
--   * Reconstructs the target enclosing widening in every branch.
--   * Contains no other QTIP application constructor, full quotient
--     recursion, QTIP-to-QTI conversion, postulate, hole, or catch-all.

import CastImprecisionShape as CastShape
import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; ∃-syntax)
open import ForallPermutation using
  (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; blame-·₁
  ; β
  ; β-↦
  ; pure-step
  ; ξ-·₁
  ; ξ-·₂
  ; _—↠[_]_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; blame
  ; no•-·
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (·₁-blame-tail)
open import proof.DGG.Core.NuPreservation using
  (runtime-⟨⟩)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  ( cast-blame-tailᵀ
  ; left-catchup-target-blameᵀ
  ; value-not-target-blameᵀ
  )
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
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationSchedulingDef
  using
  ( WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ
  ; WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ
  ; WorldCoherentRightOneStepOrdinaryDownApplicationValueRootᵀ
  )


private
  ordinary-application-left-target-blameᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M : Term} {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    RuntimeOK (L · M) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ blame
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    ∃[ χs ] ((L · M) —↠[ χs ] blame)
  ordinary-application-left-target-blameᵀ
      (ok-no (no•-· noL noM)) L⊑blame
      with left-catchup-target-blameᵀ (ok-no noL) L⊑blame
  ordinary-application-left-target-blameᵀ
      (ok-no (no•-· noL noM)) L⊑blame
      | χs , L↠blame =
    _ , ·₁-blame-tail noM L↠blame
  ordinary-application-left-target-blameᵀ
      (ok-·₁ okL noM) L⊑blame
      with left-catchup-target-blameᵀ okL L⊑blame
  ordinary-application-left-target-blameᵀ
      (ok-·₁ okL noM) L⊑blame
      | χs , L↠blame =
    _ , ·₁-blame-tail noM L↠blame
  ordinary-application-left-target-blameᵀ
      (ok-·₂ vL noL okM) L⊑blame =
    ⊥-elim (value-not-target-blameᵀ vL L⊑blame)


world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ :
  WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ →
  WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ →
  WorldCoherentRightOneStepOrdinaryDownApplicationValueRootᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ N′ : Term}
    {X X′ C C′ B B′ E E′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion}
    {μ μ′ : ModeEnv}
    {d-shape d′-shape u-shape u′-shape}
    {χ : StoreChange} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
  RuntimeOK ((L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ []
    ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ (L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩ ⦂ E′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᵇ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
  d-shape ；⌊ pX ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pE ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
  L′ · (M′ ⟨ d′ ⟩) —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = N′ ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pE
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (ξ-·₁ L′→ shift-argument) =
  function-frame
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    L′→ shift-argument
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (ξ-·₂ vL′ shift-function argument-step) =
  argument-frame
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-function argument-step
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(β v-argument)) =
  value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (ƛ _) v-argument root
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(β-↦ v-function v-argument)) =
  value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    (v-function ⟨ _ C.↦ _ ⟩) v-argument root
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑blame M⊑M′ down-square
    widening u-shape u′-shape up-square
    (pure-step blame-·₁)
    with ordinary-application-left-target-blameᵀ
      (runtime-⟨⟩ ok-source) L⊑blame
world-coherent-right-one-step-ordinary-down-application-cases-proofᵀ
    function-frame argument-frame value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑blame M⊑M′ down-square
    widening u-shape u′-shape up-square
    (pure-step blame-·₁)
    | χs , source↠blame =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ source↠blame)
