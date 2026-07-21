module
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationDef
  where

-- File Charter:
--   * Defines the fused semantic commutation boundary for a source generic
--     universal cast inside paired-lambda target closing.
--   * Retains the exact inner and generic-cast QTI relations, endpoint
--     value/bullet evidence, and recursive closing motive.
--   * Exposes no source-only intermediate relation, implementation,
--     postulate, hole, or permissive option.

import Coercions as C
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingSourceGenFrameCommutationᵀ : Set₁
PairedLambdaTargetClosingSourceGenFrameCommutationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {F B B′ : Ty} {g : Coercion}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  Value V →
  No• V →
  Value N′ →
  No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ `∀ F ⊑ `∀ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ C.gen (`∀ F) g ⟩ ⊑ N′
      ⦂ `∀ B ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    V N′ F (`∀ B′) q →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (V ⟨ C.gen (`∀ F) g ⟩) N′ B (`∀ B′) (∀ⁱ r)
