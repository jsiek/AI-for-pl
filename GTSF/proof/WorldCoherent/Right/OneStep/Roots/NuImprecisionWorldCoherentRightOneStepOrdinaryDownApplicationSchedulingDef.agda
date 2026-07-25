module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationSchedulingDef
  where

-- File Charter:
--   * Defines the three exact scheduling boundaries for an
--     `ordinary-down-applicationᵖᵀ` body beneath `up⊑upᵀ`.
--   * Separates function framing, argument framing/crossing, and the two
--     value/value application roots without converting QTIP to QTI.
--   * Keeps both narrowing casts and the enclosing quotient widening explicit.
--   * Contains no implementation, other QTIP application constructor,
--     full quotient recursion, postulate, hole, or permissive option.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; ModeEnv)
open import Data.List using ([])
open import ForallPermutation using
  (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChange
  ; Shiftable
  ; applyCoercion
  ; applyTerm
  ; keep
  ; _—→_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _⇒_)
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


WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ : Set₁
WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ L₁′ M M′ : Term}
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
  L′ —→[ χ ] L₁′ →
  Shiftable χ (M′ ⟨ d′ ⟩) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ =
      (L₁′ · applyTerm χ (M′ ⟨ d′ ⟩)) ⟨
        applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pE


WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ : Set₁
WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ M₁′ : Term}
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
  Value L′ →
  Shiftable χ L′ →
  M′ ⟨ d′ ⟩ —→[ χ ] M₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = (applyTerm χ L′ · M₁′) ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pE


WorldCoherentRightOneStepOrdinaryDownApplicationValueRootᵀ : Set₁
WorldCoherentRightOneStepOrdinaryDownApplicationValueRootᵀ =
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
    {d-shape d′-shape u-shape u′-shape} →
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
  Value L′ →
  Value (M′ ⟨ d′ ⟩) →
  L′ · (M′ ⟨ d′ ⟩) —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = N′ ⟨ u′ ⟩}
    {χ = keep} {ρ = ρ} pE
