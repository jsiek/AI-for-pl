module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  where

-- File Charter:
--   * Defines ordinary lambda-beta scheduling against a target runtime bullet.
--   * Isolates the right-world crossing from direct applications and
--     mechanical target frames.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Data.List using ([])
open import Data.Nat using (suc)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _•; ƛ_; _·_; _[_])
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceLambdaBetaTargetBulletᵀ : Set₁
WorldCoherentSourceLambdaBetaTargetBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {N V L′ : Term} {A B : Ty}
    {p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ) →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK (L′ •) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ (ƛ N) · V ⦂ A →
  suc Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ L′ • ⦂ B →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (ƛ N) · V ⊑ L′ • ⦂ A ⊑ B ∶ p →
  Value V →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = L′ •} {L = N [ V ]}
    {χ = keep} {ρ = ρ⁺} p
