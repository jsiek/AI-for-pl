module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepSourceDownApplicationCasesProof
  where

-- File Charter:
--   * Exhausts target application steps for
--     `source-down-applicationᵖᵀ` beneath `up⊑upᵀ`.
--   * Eliminates both frame cases from the stored target values and routes
--     exactly the surviving `β` and `β-↦` roots to one explicit semantic leaf.
--   * Contains no semantic-leaf implementation, QTIP-to-QTI conversion,
--     postulate, hole, permissive option, or catch-all.

import CastImprecisionShape as CastShape
import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using
  (_；_≋_; _；⌊_⌋≋ᵖ_；_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; β
  ; β-↦
  ; pure-step
  ; ξ-·₁
  ; ξ-·₂
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; ƛ_; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.DGG.Core.NuPreservation using (value-no-step)
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
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepSourceDownApplicationSchedulingDef
  using (WorldCoherentRightOneStepSourceDownApplicationValueRootᵀ)


world-coherent-right-one-step-source-down-application-cases-proofᵀ :
  WorldCoherentRightOneStepSourceDownApplicationValueRootᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ N′ : Term}
    {X C C′ B B′ E E′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ C′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {d u u′ : Coercion}
    {μ : ModeEnv}
    {d-shape u-shape u′-shape}
    {χ : StoreChange} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
  RuntimeOK ((L′ · M′) ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ []
    ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ (L′ · M′) ⟨ u′ ⟩ ⦂ E′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᵇ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pX →
  d-shape ； ⌊ pX ⌋ ≋ ⌊ pC ⌋ →
  Value L′ →
  Value M′ →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pE ⌋≋ᵖ
    (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
  L′ · M′ —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = N′ ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pE
world-coherent-right-one-step-source-down-application-cases-proofᵀ
    value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    vL′ vM′ widening u-shape u′-shape up-square
    (ξ-·₁ L′→ shift-argument) =
  ⊥-elim (value-no-step vL′ L′→)
world-coherent-right-one-step-source-down-application-cases-proofᵀ
    value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    vL′ vM′ widening u-shape u′-shape up-square
    (ξ-·₂ target-vL′ shift-function M′→) =
  ⊥-elim (value-no-step vM′ M′→)
world-coherent-right-one-step-source-down-application-cases-proofᵀ
    value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    vL′ vM′ widening u-shape u′-shape up-square
    (pure-step root@(β target-vM′)) =
  value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    (ƛ _) target-vM′ widening u-shape u′-shape up-square root
world-coherent-right-one-step-source-down-application-cases-proofᵀ
    value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    vL′ vM′ widening u-shape u′-shape up-square
    (pure-step root@(β-↦ target-vL′ target-vM′)) =
  value-root
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape L⊑L′ M⊑M′ down-triangle
    (target-vL′ ⟨ _ C.↦ _ ⟩) target-vM′
    widening u-shape u′-shape up-square root
