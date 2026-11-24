{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimBackDef where

-- File Charter:
--   * States backward simulation for a target step focused beneath the
--     canonical full-context CTI zipper.
--   * Rebuilds the complete target reduct explicitly and returns the complete
--     evolved root CTI, avoiding arbitrary sibling transport.
--   * Contains no simulation proof or residual-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; blame; ⟨_,_,_⟩)
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; _—→[_]_; _—↠[_]_ )
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; sourceTerm; targetTerm; _↘ᶜ*_ )
open import proof.DGG.SimBackContextDef using (world; RebuildTarget)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimBackᵀ : Set₁
ContextualSimBackᵀ = ∀
    {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {root focus : RelatedConfiguration
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {P′ : Term Δᴿ′} {N′ : Term Δᴿ′}
  → openFramesᶜ (world root) ≡ []
  → (path : root ↘ᶜ* focus)
  → targetTerm focus —→[ χᴿ ] P′
  → RebuildTarget path χᴿ P′ N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
        (sourceTerm root —↠[ χsᴸ ] sourceTerm root′)
        × targetTerm root′ ≡ N′
        × MultiWorldEvolution
            {W = world root} {W′ = world root′}
            χsᴸ (χᴿ ∷ˢ []ˢ))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (sourceTerm root —↠[ χsᴸ ] blame))
