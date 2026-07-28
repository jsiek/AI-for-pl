module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepSourceDownApplicationSchedulingDef
  where

-- File Charter:
--   * Defines the exact semantic leaf for the value/value application exposed
--     by `source-down-applicationᵖᵀ` beneath `up⊑upᵀ`.
--   * Keeps the source narrowing, its exact composition triangle, the outer
--     quotient widening, and the whole application context explicit.
--   * Contains no implementation, frame case, QTIP-to-QTI conversion,
--     postulate, hole, permissive option, or compatibility alias.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; ModeEnv)
open import Data.List using ([])
open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using
  (_；_≋_; _；⌊_⌋≋ᵖ_；_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
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


WorldCoherentRightOneStepSourceDownApplicationValueRootᵀ : Set₁
WorldCoherentRightOneStepSourceDownApplicationValueRootᵀ =
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
    {d-shape u-shape u′-shape} →
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
  L′ · M′ —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
    {N′ = N′ ⟨ u′ ⟩}
    {χ = keep} {ρ = ρ} pE
