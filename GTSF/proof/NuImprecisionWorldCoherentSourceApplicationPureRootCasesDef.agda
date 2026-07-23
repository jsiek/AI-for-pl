module
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  where

-- File Charter:
--   * Defines the two semantic beta capabilities needed by source
--     application pure roots.
--   * Keeps lambda substitution and function-coercion beta separate so each
--     can be proved and checked independently.
--   * Reuses the canonical source-blame root outside this record and contains
--     no result wrapper, implementation, postulate, hole, or option.

import Coercions as C
open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceLambdaBetaRootᵀ : Set₁
WorldCoherentSourceLambdaBetaRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ (ƛ N) · V ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (ƛ N) · V ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value V →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = M′} {L = N [ V ]}
    {χ = keep} {ρ = ρ⁺} p


WorldCoherentSourceFunctionCastBetaRootᵀ : Set₁
WorldCoherentSourceFunctionCastBetaRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V W M′ : Term} {c d : C.Coercion} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ (V ⟨ c C.↦ d ⟩) · W ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (V ⟨ c C.↦ d ⟩) · W ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value V →
  Value W →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = M′} {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ⁺} p


record WorldCoherentSourceApplicationPureRootCases : Set₁ where
  field
    sourceLambdaBetaRootCase :
      WorldCoherentSourceLambdaBetaRootᵀ

    sourceFunctionCastBetaRootCase :
      WorldCoherentSourceFunctionCastBetaRootᵀ

open WorldCoherentSourceApplicationPureRootCases public
