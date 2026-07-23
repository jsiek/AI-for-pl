module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetBulletFrameStepDef
  where

-- File Charter:
--   * Defines the hard source-step crossing for a target runtime-bullet node.
--   * Returns the existing source-step outcome directly across the right-world
--     lift; no bullet-specific result or outcome carrier escapes.
--   * Contains no implementation, postulate, hole, permissive option, or
--     compatibility alias.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuReduction using (StoreChange; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _•; ⇑ᵗᵐ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (WorldCoherentSourceOneStepOutcome)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


WorldCoherentSourceOneStepTargetBulletFrameStepᵀ : Set₁
WorldCoherentSourceOneStepTargetBulletFrameStepᵀ =
  WorldCoherentSourceOneStepPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {N N₁ L′ : Term} {A B C′ : Ty}
    {χ : StoreChange}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  StoreImpPrefix
    (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK N →
  RuntimeOK ((⇑ᵗᵐ L′) •) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ B →
  suc Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ []
    ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ N ⦂ B →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  N —→[ χ ] N₁ →
  WorldCoherentSourceOneStepOutcome
    {M = N} {M′ = (⇑ᵗᵐ L′) •} {L = N₁}
    {A = B} {B = C′} {χ = χ} {ρ = ρ⁺} r
