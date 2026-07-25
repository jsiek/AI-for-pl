module proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesDef where

-- File Charter:
--   * Defines the four source-frame capabilities used by recursive
--     world-coherent right-value catch-up.
--   * Keeps every ambient-prefix, runtime, cast, relation, and recursive
--     result premise explicit at the canonical source-frame boundary.
--   * Contains no dispatcher, implementation, postulate, hole, or permissive
--     option.

open import Data.List using ([])

open import Coercions using (Coercion; Inert)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; narrowing; widening)
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
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


record WorldCoherentRightSourceFrames : Set₁ where
  field
    rightSourceNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} {s} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK M′ →
      Value M →
      No• M →
      Inert c →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
      narrowing ⊢ᶜ c ⦂ s →
      s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q

    rightSourceWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} {s} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK M′ →
      Value M →
      No• M →
      Inert c →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q

    rightSourceRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ α X}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK M′ →
      Value M →
      No• M →
      Inert c →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      p [ α ↦ X ]ᴸ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q

    rightSourceConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ α X}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK M′ →
      Value M →
      No• M →
      Inert c →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      q [ α ↦ X ]ᴸ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q

open WorldCoherentRightSourceFrames public
