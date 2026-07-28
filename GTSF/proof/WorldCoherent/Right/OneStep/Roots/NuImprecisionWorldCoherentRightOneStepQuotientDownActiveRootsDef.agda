module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveRootsDef
  where

-- File Charter:
--   * Defines the feasible target-root cells for exact active target-down
--     synchronization inside the `paired-downᵀ` spine modes.
--   * Separates identity, sequence, and untag roots while retaining the
--     enclosing quotient-widening pair, compatibility, and both composition
--     squares.
--   * Leaves instantiation, unseal, and target blame elimination to the
--     dispatcher proof.
--   * Contains no implementation, frame recursion, postulate, hole,
--     permissive option, compatibility alias, or application case.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; id; _︔_; _？)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import Types using (Ty; TyCtx)
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
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (QuotientDownMode; quotient-down-mode)


record WorldCoherentRightOneStepQuotientDownActiveRoots : Set₁ where
  field
    rightStepQuotientDownIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ L′ : Term} {C C′ D D′ A A′ I : Ty}
        {d u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      (down-mode : QuotientDownMode) →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
      RuntimeOK ((V′ ⟨ id I ⟩) ⟨ u′ ⟩) →
      Value V′ →
      quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
        ⊢ d ∶ C ⊒ D →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
        ⊢ id I ∶ C′ ⊒ D′ →
      CastShape.narrowing CastShape.⊢ᶜ id I ⦂ d′-shape →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
      d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
      CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
      CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
      V′ ⟨ id I ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (M ⟨ d ⟩) ⟨ u ⟩}
        {N′ = L′ ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA

    rightStepQuotientDownSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ L′ : Term} {C C′ D D′ A A′ : Ty}
        {d s t u u′ : Coercion}
        {d-shape d′-shape u-shape u′-shape}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      (down-mode : QuotientDownMode) →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
      RuntimeOK ((V′ ⟨ s ︔ t ⟩) ⟨ u′ ⟩) →
      Value V′ →
      quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
        ⊢ d ∶ C ⊒ D →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
        ⊢ s ︔ t ∶ C′ ⊒ D′ →
      CastShape.narrowing CastShape.⊢ᶜ s ︔ t ⦂ d′-shape →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
      d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
      CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
      CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
      V′ ⟨ s ︔ t ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (M ⟨ d ⟩) ⟨ u ⟩}
        {N′ = L′ ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA

    rightStepQuotientDownUntagRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ L′ : Term} {C C′ D D′ A A′ H : Ty}
        {d u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      (down-mode : QuotientDownMode) →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
      RuntimeOK ((V′ ⟨ H ？ ⟩) ⟨ u′ ⟩) →
      Value V′ →
      quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
        ⊢ d ∶ C ⊒ D →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
        ⊢ H ？ ∶ C′ ⊒ D′ →
      CastShape.narrowing CastShape.⊢ᶜ H ？ ⦂ d′-shape →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
      d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
      CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
      CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
      V′ ⟨ H ？ ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (M ⟨ d ⟩) ⟨ u ⟩}
        {N′ = L′ ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA

open WorldCoherentRightOneStepQuotientDownActiveRoots public
