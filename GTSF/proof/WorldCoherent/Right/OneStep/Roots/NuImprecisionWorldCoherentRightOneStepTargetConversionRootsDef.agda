module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsDef
  where

-- File Charter:
--   * Defines the complete target-oriented active target-conversion roots.
--   * Retains the exact right-index replacement selected by QTI.
--   * Excludes target-conversion context frames, recursion, postulates, holes,
--     and permissive options.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; _—→_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
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
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepTargetConversionRoots : Set₁ where
  field
    rightStepTargetRevealConversionRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B′ : Ty}
        {c′ μ′ β X′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ A′ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      p [ β ↦ X′ ]ᴿ q →
      M′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetConcealConversionRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B′ : Ty}
        {c′ μ′ β X′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ A′ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      q [ β ↦ X′ ]ᴿ p →
      M′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepTargetConversionRoots public
