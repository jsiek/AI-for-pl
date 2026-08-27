{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceRebaseStackDef where

-- File Charter:
--   * States CTI transport along a balanced source-rebase stack evolution.
--   * Uses the top history selected by the stack evolution and returns the
--     transported CTI directly, with no arbitrary world pullback.

open import Types using (Ty)
open import CastTerms using (Term; Δᵉ)
open import Reduction using
  (StoreChanges; applyTerms; applyTys)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebaseStackDef using
  ( SourceRebaseStack
  ; SourceRebaseStackEvolution
  ; stack-top-evolution
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (multi-⊑ᵀ)


TransportSourceRebaseStackᵀ : Set
TransportSourceRebaseStackᵀ = ∀
    {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : CastTerms.Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {γ⁰′ γ′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {stack : SourceRebaseStack γ⁰ γ}
    {stack′ : SourceRebaseStack γ⁰′ γ′}
    {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ Cᴿ)}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → (evolution : SourceRebaseStackEvolution
      {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack′)
  → {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → γ′ ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
      ∶ multi-⊑ᵀ (stack-top-evolution evolution) p
