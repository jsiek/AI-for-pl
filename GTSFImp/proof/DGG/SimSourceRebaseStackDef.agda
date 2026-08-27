{-# OPTIONS --safe #-}

module proof.DGG.SimSourceRebaseStackDef where

-- File Charter:
--   * States forward simulation under a balanced stack of open source-rebase
--     scopes.
--   * Returns the evolved root, top, stack, target trace, and CTI directly.
--   * Is the genuine world-history induction used before a target reveal can
--     close one source-rebase scope; it has no classifier or result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; ⟨_,_,_⟩)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebaseStackDef using
  ( SourceRebaseStack
  ; SourceRebaseStackEvolution
  )
open import proof.DGG.World


SimSourceRebaseStackᵀ : Set
SimSourceRebaseStackᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ⁰ γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , [] ⟩}
    {stack : SourceRebaseStack γ⁰ γ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ⁰′ ∈
      (⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ γ′ ∈
      (⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ stack′ ∈ SourceRebaseStack γ⁰′ γ′ ]
    Σ[ q ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × SourceRebaseStackEvolution
          {χsᴸ = χᴸ ∷ˢ []ˢ} {χsᴿ = χsᴿ} stack stack′
      × (γ′ ⊢² N ⊑ N′ ∶ q)
