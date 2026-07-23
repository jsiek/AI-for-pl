module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  where

-- File Charter:
--   * Defines direct target scheduling for an ordinary source lambda beta.
--   * Starts after inversion has exposed an unframed target application and
--     the related function and argument premises.
--   * Contains no dispatcher, implementation, result wrapper, postulate,
--     hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; ƛ_; _·_; _[_])
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceLambdaBetaDirectᵀ : Set₁
WorldCoherentSourceLambdaBetaDirectᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V L′ R′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK (L′ · R′) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ (ƛ N) · V ⦂ B →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ L′ · R′ ⦂ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ƛ N ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = L′ · R′} {L = N [ V ]}
    {χ = keep} {ρ = ρ⁺} pB
