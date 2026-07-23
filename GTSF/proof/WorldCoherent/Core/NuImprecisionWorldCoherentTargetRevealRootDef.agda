module proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetRevealRootDef where

-- File Charter:
--   * Defines the world-coherent target reveal-unseal root contract.
--   * Exposes the exact target-store membership needed to cancel the seal.
--   * Contains no implementation or recursive simulation dependency.

open import Coercions using (seal)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyVar; ＇_)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentTargetRevealRootᵀ : Set₁
WorldCoherentTargetRevealRootᵀ =
  ∀ {Φ Δᴸ Δᴿ} {M V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (V ⟨ seal X β ⟩) →
  Value V →
  (β , X′) ∈ rightStoreⁱ ρ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⟨ seal X β ⟩ ⦂ A ⊑ ＇ β ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
