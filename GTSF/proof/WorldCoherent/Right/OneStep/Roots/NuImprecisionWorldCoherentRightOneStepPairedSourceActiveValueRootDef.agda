module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  where

-- File Charter:
--   * Defines the three live paired outer-cast value roots for an arbitrary
--     source inner term when the source cast is non-inert.
--   * Carries exact reveal, conceal, or widening constructor evidence;
--     casted endpoint syntax is never used as an inversion principle.
--   * Contains no implementation, source-inert fallback, quotient case,
--     recursive dispatcher, postulate, hole, or permissive option.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar)
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


record WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ : Set₁ where
  field
    active-paired-reveal-root :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ N′ : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
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
      (Inert c → ⊥) →
      StoreCorresponds ρ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ A′ B′ →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

    active-paired-conceal-root :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ N′ : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
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
      (Inert c → ⊥) →
      StoreCorresponds ρ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ A′ B′ →
      q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

    active-paired-widening-root :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V′ N′ : Term} {A A′ B B′ : Ty}
        {c c′ : Coercion} {μ μ′ : ModeEnv}
        {s s′ t : ImprecisionShape}
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
      (Inert c → ⊥) →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s′ →
      s ； ⌊ q ⌋ ≋ t →
      ⌊ p ⌋ ； s′ ≋ t →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ public
