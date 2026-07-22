module proof.NuImprecisionWorldCoherentRightSourceAllClosingDef where

-- File Charter:
--   * Defines the world-coherent right source-universal closing capability.
--   * Keeps the source-only binder allocation, occurrence evidence, lifted
--     relation, and indexed closing result explicit at this boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
import ImprecisionWf as IW
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value; Λ_)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; occurs)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightSourceAllClosingᵀ : Set₁
WorldCoherentRightSourceAllClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {occ : occurs zero A ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ V} {M′ = N′} {ρ = ρ⁺} (IW.ν occ p)
