module proof.NuImprecisionWorldCoherentSourcePureStepCasesDef where

-- File Charter:
--   * Defines the exact world-coherent source pure-step boundary.
--   * Partitions pure roots by their four exhaustive outer source shapes.
--   * Keeps ambient-prefix, refined typing, runtime, store, and world
--     premises explicit in every major capability.
--   * Contains no dispatcher, semantic implementation, postulate, or hole.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; _·_; _•; _⟨_⟩; _⊕[_]_)
open import Primitives using (Prim)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourcePureStepᵀ : Set₁
WorldCoherentSourcePureStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→ L →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L} {χ = keep} {ρ = ρ⁺} p


record WorldCoherentSourcePureStepCases : Set₁ where
  field
    sourceApplicationPureRootCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {F V M′ L : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (F · V) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ F · V ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ F · V ⊑ M′ ⦂ A ⊑ B ∶ p →
      F · V —→ L →
      WorldCoherentSourceOneStepIndexedResult
        {M = F · V} {M′ = M′} {L = L}
        {χ = keep} {ρ = ρ⁺} p

    sourceRuntimeBulletPureRootCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {F M′ L : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (F •) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ F • ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ F • ⊑ M′ ⦂ A ⊑ B ∶ p →
      F • —→ L →
      WorldCoherentSourceOneStepIndexedResult
        {M = F •} {M′ = M′} {L = L}
        {χ = keep} {ρ = ρ⁺} p

    sourceCastPureRootCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ L : Term} {c : Coercion} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (V ⟨ c ⟩) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ V ⟨ c ⟩ ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⟨ c ⟩ ⊑ M′ ⦂ A ⊑ B ∶ p →
      V ⟨ c ⟩ —→ L →
      WorldCoherentSourceOneStepIndexedResult
        {M = V ⟨ c ⟩} {M′ = M′} {L = L}
        {χ = keep} {ρ = ρ⁺} p

    sourcePrimitivePureRootCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {L R M′ N : Term} {op : Prim} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
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

open WorldCoherentSourcePureStepCases public
