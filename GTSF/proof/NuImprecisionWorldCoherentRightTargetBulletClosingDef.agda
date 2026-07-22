module proof.NuImprecisionWorldCoherentRightTargetBulletClosingDef where

-- File Charter:
--   * Defines the world-coherent right target-bullet closing capability.
--   * Keeps the right allocation prefix, lifted relation, endpoint typings,
--     and indexed bullet result explicit at this semantic boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightCtxⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using (No•; RuntimeOK; Term; Value; ⇑ᵗᵐ; _•)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetBulletClosingᵀ : Set₁
WorldCoherentRightTargetBulletClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {A B C′ : Ty} {N L′ : Term}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    {ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  StoreImpPrefix (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK ((⇑ᵗᵐ L′) •) →
  Value N →
  No• N →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    (⇑ᴿᵢ Φ) [] [] →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  Δᴸ ∣ leftStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ N ⦂ B →
  suc Δᴿ ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = N} {M′ = (⇑ᵗᵐ L′) •} {ρ = ρ⁺} r
