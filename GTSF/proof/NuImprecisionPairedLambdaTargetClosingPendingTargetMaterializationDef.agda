module
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetMaterializationDef
  where

-- File Charter:
--   * Defines materialization of a pending target-only frame continuation.
--   * The conclusion exposes the final target value, no-bullet evidence, and
--     quotiented term-imprecision derivation at the continuation's final
--     relational-store world and imprecision index.
--   * Contains no implementation, postulate, hole, permissive option,
--     terminal closing theorem, semantic handler, or broad simulation import.

open import Data.List using ([])
open import Data.Product using (_×_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingPendingTargetFrames)


PairedLambdaTargetClosingPendingTargetMaterializationᵀ : Set₁
PairedLambdaTargetClosingPendingTargetMaterializationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ W⁺ : Term} {F B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ} →
  Value W′ →
  No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ F ⊑ B′ ∶ q →
  PairedLambdaTargetClosingPendingTargetFrames
    ρ₀ W W′ F B′ q ρ⁺ W⁺ C′ r →
  Value W⁺ ×
  No• W⁺ ×
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ W ⊑ W⁺ ⦂ `∀ F ⊑ C′ ∶ r
