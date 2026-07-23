module proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupDef where

-- File Charter:
--   * Defines the lifted-world recursive call used by source-universal
--     right-value closing.
--   * Returns the existing catch-up result together with the lifted ambient
--     store and its prefix, without adding a result or view hierarchy.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; ∃-syntax)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightSourceAllBodyCatchupᵀ : Set₁
WorldCoherentRightSourceAllBodyCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∃[ ρ⁺ᴸ ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ⁺ ρ⁺ᴸ ×
    StoreImpPrefix ρᴸ ρ⁺ᴸ ×
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = N′} {ρ = ρ⁺ᴸ} p
