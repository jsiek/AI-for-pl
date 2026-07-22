module
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootDef
  where

-- File Charter:
--   * Defines the exact world-coherent source primitive pure-root boundary.
--   * Keeps ambient-prefix, refined typing, runtime, store, world, relation,
--     reduction, and strong-result premises explicit.
--   * Contains no implementation, dispatcher, postulate, hole, or option.

open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; _⊕[_]_)
open import Primitives using (Prim)
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


WorldCoherentSourcePrimitivePureRootᵀ : Set₁
WorldCoherentSourcePrimitivePureRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {L R M′ N : Term} {op : Prim} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (L ⊕[ op ] R) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ L ⊕[ op ] R ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊕[ op ] R ⊑ M′ ⦂ A ⊑ B ∶ p →
  L ⊕[ op ] R —→ N →
  WorldCoherentSourceOneStepIndexedResult
    {M = L ⊕[ op ] R} {M′ = M′} {L = N}
    {χ = keep} {ρ = ρ⁺} p
