module
  proof.NuImprecisionWorldCoherentSourceCastPureRootDef
  where

-- File Charter:
--   * Defines the exact world-coherent source cast-root capability.
--   * Covers pure roots whose source applies a cast or conversion to a value.
--   * Keeps the full ambient-prefix and strong-result boundary explicit.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceCastPureRootᵀ : Set₁
WorldCoherentSourceCastPureRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ L : Term} {c : Coercion} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (V ⟨ c ⟩) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ V ⟨ c ⟩ ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ c ⟩ ⊑ M′ ⦂ A ⊑ B ∶ p →
  V ⟨ c ⟩ —→ L →
  WorldCoherentSourceOneStepIndexedResult
    {M = V ⟨ c ⟩} {M′ = M′} {L = L}
    {χ = keep} {ρ = ρ⁺} p
