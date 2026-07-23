module proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef where

-- File Charter:
--   * Defines the ordinary and casted right target-allocation frame cases.
--   * Keeps reveal/cast evidence, lifted right stores and contexts, recursive
--     results, and final indexed allocation results explicit at this boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightCtxⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value; ν)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; ★; `∀; ⟰ᵗ; ⇑ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightTargetAllocationFrames : Set₁ where
  field
    rightTargetNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {A B B′ C′ : Ty} {N N′ : Term} {s : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν A N′ s) →
      Value N →
      No• N →
      WfTy Δᴿ A →
      WfTy (suc Δᴿ) (⇑ᵗ A) →
      RevealConversion μ (suc Δᴿ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ′ →
      LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        (⇑ᴿᵢ Φ) [] [] →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = N′} {ρ = ρ⁺} q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = ν A N′ s} {ρ = ρ⁺} p

    rightTargetNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {B B′ C′ : Ty} {N N′ : Term} {s : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν ★ N′ s) →
      Value N →
      No• N →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴿ
        ∣ ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ′ →
      LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        (⇑ᴿᵢ Φ) [] [] →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = N′} {ρ = ρ⁺} q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = ν ★ N′ s} {ρ = ρ⁺} p

open WorldCoherentRightTargetAllocationFrames public
