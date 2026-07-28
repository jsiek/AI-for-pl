module proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedFramesDef where

-- File Charter:
--   * Defines the three live world-coherent right paired-cast frame
--     capabilities.
--   * Keeps exact paired reveal, conceal, and widening constructor evidence
--     explicit; casted endpoint syntax is never used for inversion.
--   * Contains no implementation, retired paired-cast abstraction,
--     dispatcher, postulate, hole, or permissive option.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([])
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import
  proof.Store.Core.NuImprecisionRelationalStoreDef
  using
  ( StoreCorresponds
  ; StoreImp
  ; rightStoreⁱ
  ; leftStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; TyVar)
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
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightPairedFramesᵀ : Set₁ where
  field
    rightPairedRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value M →
      No• M →
      Inert c →
      StoreCorresponds ρ₀ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightPairedConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value M →
      No• M →
      Inert c →
      StoreCorresponds ρ₀ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightPairedWideningFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B B′ : Ty}
        {c c′ : Coercion} {μ μ′ : ModeEnv}
        {s s′ r : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value M →
      No• M →
      Inert c →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s′ →
      s ； ⌊ q ⌋ ≋ r →
      ⌊ p ⌋ ； s′ ≋ r →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

open WorldCoherentRightPairedFramesᵀ public
