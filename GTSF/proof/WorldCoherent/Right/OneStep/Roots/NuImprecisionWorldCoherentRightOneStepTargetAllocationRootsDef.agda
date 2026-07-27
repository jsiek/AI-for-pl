module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  where

-- File Charter:
--   * Defines the matched reveal-ν target-allocation root for target-oriented
--     world-coherent one-step simulation.
--   * Retains the paired replacement witness.
--   * Excludes the separate `blame-ν` root and contains no implementation,
--     dispatcher, postulate, hole, permissive option, or broad simulation
--     import.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (bind; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-target-lift-rightᵢ)
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


record WorldCoherentRightOneStepTargetAllocationRoots : Set₁ where
  field
    rightStepMatchedNuAllocationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {A A′ B B′ C C′ : Ty} {N V′ N′ : Term}
        {s s′ : Coercion} {μ μ′}
        {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (ν A N s) →
      RuntimeOK (ν A′ V′ s′) →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
      q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB →
      ν A′ V′ s′ —→[ bind A′ ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν A N s} {N′ = N′}
        {χ = bind A′} {ρ = ρ} pB

open WorldCoherentRightOneStepTargetAllocationRoots public
