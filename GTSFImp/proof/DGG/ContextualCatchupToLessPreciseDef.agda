{-# OPTIONS --safe #-}

module proof.DGG.ContextualCatchupToLessPreciseDef where

-- File Charter:
--   * States source value catch-up beneath the canonical full-context CTI
--     zipper while retaining the whole related root.
--   * Returns an evolved root-to-focus path, so callers rebuild application,
--     primitive, and result-conversion contexts without sibling transport.
--   * Contains no catch-up proof or residual-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Value; blame; ⟨_,_,_⟩)
open import Reduction using (StoreChanges; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; sourceTerm; targetTerm; _↘ᶜ*_ )
open import proof.DGG.SimBackContextDef using
  (world; SourcePathEvolution)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualCatchupToLessPreciseᵀ : Set₁
ContextualCatchupToLessPreciseᵀ = ∀
    {Δᴸ Δᴿ : TyCtx} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {root focus : RelatedConfiguration
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩}
  → openFramesᶜ (world root) ≡ []
  → (path : root ↘ᶜ* focus)
  → Value (targetTerm focus)
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ focus′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ path′ ∈ root′ ↘ᶜ* focus′ ]
        (sourceTerm root —↠[ χsᴸ ] sourceTerm root′)
        × Value (sourceTerm focus′)
        × targetTerm root′ ≡ targetTerm root
        × targetTerm focus′ ≡ targetTerm focus
        × SourcePathEvolution path path′
        × MultiWorldEvolution
            {W = world root} {W′ = world root′} χsᴸ []ˢ)
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (sourceTerm root —↠[ χsᴸ ] blame)
        × MultiWorldEvolution
            {W = world root} {W′ = γ′} χsᴸ []ˢ)
