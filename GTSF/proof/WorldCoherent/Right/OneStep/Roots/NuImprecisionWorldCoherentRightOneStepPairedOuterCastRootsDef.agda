module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsDef
  where

-- File Charter:
--   * Defines the four paired outer-cast cells in target-oriented one-step
--     simulation: ordinary paired-cast framing and value roots, plus quotient
--     widening framing and value roots.
--   * Retains each exact PairedCast or QuotientWideningPair, both quotient
--     cast shapes, the quotient composition square, and the complete
--     world-coherent outcome with relational-store lineage.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or theorem-fragment alias.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion)
open import Data.List using ([])
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; applyCoercion; keep; _—→_; _—→[_]_)
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
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
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


record WorldCoherentRightOneStepPairedOuterCastRoots : Set₁ where
  field
    rightStepPairedCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B B′ : Ty}
        {c c′ : Coercion} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
      M′ —→[ χ ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩}
        {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} q

    rightStepPairedCastValueRoot :
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

    rightStepQuotientWideningFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N N′ L′ : Term} {D D′ A A′ : Ty}
        {u u′ : Coercion} {s s′}
        {χ : StoreChange}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (N′ ⟨ u′ ⟩) →
      Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ N ⟨ u ⟩ ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ N′ ⟨ u′ ⟩ ⦂ A′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ s →
      widening ⊢ᶜ u′ ⦂ s′ →
      s ；⌊ pA ⌋≋ᵖ qD ； s′ →
      N′ —→[ χ ] L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩}
        {N′ = L′ ⟨ applyCoercion χ u′ ⟩}
        {χ = χ} {ρ = ρ} pA

    rightStepQuotientWideningValueRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ L′ : Term} {D D′ A A′ : Ty}
        {u u′ : Coercion} {s s′}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (V′ ⟨ u′ ⟩) →
      Value V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ s →
      widening ⊢ᶜ u′ ⦂ s′ →
      s ；⌊ pA ⌋≋ᵖ qD ； s′ →
      V′ ⟨ u′ ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩} {N′ = L′}
        {χ = keep} {ρ = ρ} pA

open WorldCoherentRightOneStepPairedOuterCastRoots public
