{-# OPTIONS --safe #-}

module proof.DGG.TransportTargetTermImprecisionDef where

-- File Charter:
--   * States CTI transport through target-only multi-world evolution.
--   * Fixes the source endpoint and source term while the target store and
--     target term evolve.
--   * Excludes source allocation, including aligned source allocation, by
--     requiring the source store-change trace to be empty.
--   * Contains no transport proof.

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using (StoreChanges; applyTerms)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution; multi-⊑ᵀ)


TransportTargetTermImprecisionᵀ : Set
TransportTargetTermImprecisionᵀ = ∀
    {Γᴸ Γᴿ Γᴿ′ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {γ′ : Γᴸ ⊑ᶜ Γᴿ′}
    {χsᴿ : StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′)}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (evolution : MultiWorldEvolution
      {W = γ} {W′ = γ′} []ˢ χsᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ′ ⊢² M ⊑ applyTerms χsᴿ M′
      ∶ multi-⊑ᵀ evolution p
