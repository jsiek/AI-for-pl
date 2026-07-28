module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRootsDef
  where

-- File Charter:
--   * Defines the three feasible semantic roots for an active target
--     narrowing in the argument of `ordinary-down-applicationᵖᵀ`.
--   * Keeps arbitrary cast modes, the whole application context, both
--     quotient boundary squares, and the enclosing quotient widening.
--   * Separates identity, sequence, and untag roots; narrowing excludes
--     instantiation and unseal roots, while a value body excludes blame.
--   * Contains no implementation, QTIP-to-QTI conversion, postulate, hole,
--     permissive option, compatibility alias, or unrelated application root.

import CastImprecisionShape as CastShape
open import Coercions using
  (Coercion; ModeEnv; id; _︔_; _？)
open import Data.List using ([])
open import ForallPermutation using
  (≈∀-refl; quotientᵖ)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  (keep; _—→_)
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


record
  WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRoots :
    Set₁
  where
  field
    rightStepOrdinaryDownApplicationIdentityArgumentRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ M M′ M₁′ : Term}
        {X X′ C C′ B B′ E E′ I : Ty}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {d u u′ : Coercion}
        {μ μ′ : ModeEnv}
        {d-shape d′-shape u-shape u′-shape} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
      RuntimeOK ((L′ · (M′ ⟨ id I ⟩)) ⟨ u′ ⟩) →
      Δᴸ ∣ leftStoreⁱ ρ ∣ []
        ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
      Δᴿ ∣ rightStoreⁱ ρ ∣ []
        ⊢ (L′ · (M′ ⟨ id I ⟩)) ⟨ u′ ⟩ ⦂ E′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᵇ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ id I ∶ X′ ⊒ C′ →
      CastShape.narrowing CastShape.⊢ᶜ id I ⦂ d′-shape →
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
      Value M′ →
      M′ ⟨ id I ⟩ —→ M₁′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
        {N′ = (L′ · M₁′) ⟨ u′ ⟩}
        {χ = keep} {ρ = ρ} pE

    rightStepOrdinaryDownApplicationSequenceArgumentRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ M M′ M₁′ : Term}
        {X X′ C C′ B B′ E E′ : Ty}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {d s t u u′ : Coercion}
        {μ μ′ : ModeEnv}
        {d-shape d′-shape u-shape u′-shape} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
      RuntimeOK ((L′ · (M′ ⟨ s ︔ t ⟩)) ⟨ u′ ⟩) →
      Δᴸ ∣ leftStoreⁱ ρ ∣ []
        ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
      Δᴿ ∣ rightStoreⁱ ρ ∣ []
        ⊢ (L′ · (M′ ⟨ s ︔ t ⟩)) ⟨ u′ ⟩ ⦂ E′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᵇ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ s ︔ t ∶ X′ ⊒ C′ →
      CastShape.narrowing CastShape.⊢ᶜ s ︔ t ⦂ d′-shape →
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
      Value M′ →
      M′ ⟨ s ︔ t ⟩ —→ M₁′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
        {N′ = (L′ · M₁′) ⟨ u′ ⟩}
        {χ = keep} {ρ = ρ} pE

    rightStepOrdinaryDownApplicationUntagArgumentRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ M M′ M₁′ : Term}
        {X X′ C C′ B B′ E E′ H : Ty}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {d u u′ : Coercion}
        {μ μ′ : ModeEnv}
        {d-shape d′-shape u-shape u′-shape} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
      RuntimeOK ((L′ · (M′ ⟨ H ？ ⟩)) ⟨ u′ ⟩) →
      Δᴸ ∣ leftStoreⁱ ρ ∣ []
        ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
      Δᴿ ∣ rightStoreⁱ ρ ∣ []
        ⊢ (L′ · (M′ ⟨ H ？ ⟩)) ⟨ u′ ⟩ ⦂ E′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᵇ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ H ？ ∶ X′ ⊒ C′ →
      CastShape.narrowing CastShape.⊢ᶜ H ？ ⦂ d′-shape →
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
      Value M′ →
      M′ ⟨ H ？ ⟩ —→ M₁′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
        {N′ = (L′ · M₁′) ⟨ u′ ⟩}
        {χ = keep} {ρ = ρ} pE

open
  WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRoots
  public
