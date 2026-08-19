module proof.DGG.Parked.ParkedEvolveCompositionDef where

-- File Charter:
--   * States transitive composition for two-sided parked-world evolution.
--   * Uses the canonical store-change append operation shared by DGG traces.
--   * Contains no composition proof.

open import Types using (TyCtx)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef using (ParkedEvolve)
open import proof.Reduction using (_++χ_)
open CTX using (World)


ComposeParkedEvolveᵀ : Set
ComposeParkedEvolveᵀ =
  ∀ {Δᴸ₀ Δᴸ₁ Δᴸ₂ Δᴿ₀ Δᴿ₁ Δᴿ₂ : TyCtx}
    {Δ₀ Δ₁ Δ₂ : TyCtx}
    {χsᴸ : StoreChanges Δᴸ₀ Δᴸ₁}
    {ψsᴸ : StoreChanges Δᴸ₁ Δᴸ₂}
    {χsᴿ : StoreChanges Δᴿ₀ Δᴿ₁}
    {ψsᴿ : StoreChanges Δᴿ₁ Δᴿ₂}
    {W₀ : World Δᴸ₀ Δᴿ₀ Δ₀}
    {W₁ : World Δᴸ₁ Δᴿ₁ Δ₁}
    {W₂ : World Δᴸ₂ Δᴿ₂ Δ₂}
  → ParkedEvolve χsᴸ χsᴿ W₀ W₁
  → ParkedEvolve ψsᴸ ψsᴿ W₁ W₂
  → ParkedEvolve (χsᴸ ++χ ψsᴸ) (χsᴿ ++χ ψsᴿ) W₀ W₂
