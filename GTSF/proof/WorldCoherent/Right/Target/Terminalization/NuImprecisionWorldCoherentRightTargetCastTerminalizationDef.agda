module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  where

-- File Charter:
--   * Defines the five target-cast terminalization capabilities used by
--     recursive world-coherent right-value catch-up.
--   * Keeps every ambient-prefix, runtime, cast, relation, and recursive
--     result premise explicit at the canonical target-frame boundary.
--   * Each capability includes both inert framing and active-root
--     normalization needed to finish at a target value.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import Data.List using ([])

open import CastImprecisionShape using (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using (Coercion; id-onlyᵈ)
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightTargetCastTerminalization : Set₁ where
  field
    rightTargetNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A A′ B′ : Ty} {c′ : Coercion} {μ′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value V →
      No• V →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊒ B′ →
      narrowing ⊢ᶜ c′ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightTargetWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A A′ B′ : Ty} {c′ : Coercion} {μ′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value V →
      No• V →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightTargetIdWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A A′ B′ : Ty} {c′ : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value V →
      No• V →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightTargetRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A A′ B′ : Ty} {c′ : Coercion} {μ′ β X′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value V →
      No• V →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      p [ β ↦ X′ ]ᴿ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    rightTargetConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A A′ B′ : Ty} {c′ : Coercion} {μ′ β X′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      Value V →
      No• V →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      q [ β ↦ X′ ]ᴿ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q

open WorldCoherentRightTargetCastTerminalization public
