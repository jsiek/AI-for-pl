module
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationDef
  where

-- File Charter:
--   * Defines the fused semantic commutation boundary for one structural
--     source-universal frame inside target closing.
--   * Retains the exact inner and framed quotiented relations, endpoint
--     value/bullet evidence, and recursive closing motive.
--   * Exposes no source-only intermediate relation, implementation,
--     postulate, hole, or permissive option.

import Coercions as C
open import Coercions using (Coercion)
open import Data.List using ([])
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingSourceAllFrameCommutationᵀ : Set₁
PairedLambdaTargetClosingSourceAllFrameCommutationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ : Ty} {d : Coercion}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ B ⊑ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⟨ C.`∀ d ⟩ ⊑ W′ ⦂ `∀ C ⊑ B′ ∶ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ d ⟩) W′ C B′ r
