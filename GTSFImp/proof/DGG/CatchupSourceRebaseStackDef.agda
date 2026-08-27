{-# OPTIONS --safe #-}

module proof.DGG.CatchupSourceRebaseStackDef where

-- File Charter:
--   * States target value catch-up beneath a balanced source-rebase stack.
--   * Returns the evolved stack, target value trace, and CTI directly.
--   * Preserves runtime chronology through SourceRebaseStackEvolution.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebaseStackDef using
  ( SourceRebaseStack
  ; SourceRebaseStackEvolution
  )
open import proof.DGG.World


CatchupSourceRebaseStackᵀ : Set
CatchupSourceRebaseStackᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ⁰ γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , [] ⟩}
    {stack : SourceRebaseStack γ⁰ γ}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² V ⊑ M′ ∶ p
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ]
    Σ[ γ⁰′ ∈
      (⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ γ′ ∈
      (⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ stack′ ∈ SourceRebaseStack γ⁰′ γ′ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] V′)
      × Value V′
      × SourceRebaseStackEvolution
          {χsᴸ = []ˢ} {χsᴿ = χsᴿ} stack stack′
      × (γ′ ⊢² V ⊑ V′ ∶ q)
