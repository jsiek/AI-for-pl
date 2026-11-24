{-# OPTIONS --safe #-}

module proof.DGG.SimPrimitiveValuesDef where

-- File Charter:
--   * States primitive delta simulation after both target operands have
--     caught up to related values.
--   * Exposes the target delta trace, synchronized world evolution, and final
--     constant relation directly.
--   * Contains no primitive-value proof or catch-up wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (TyCtx)
open import TyStore using (TyStore)
open import Primitives using (primArgTy; primResultTy; δ)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; $; _⊕[_]_)
open import Reduction using
  ( StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; keep
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimPrimitiveValuesᵀ : Set
SimPrimitiveValuesᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {op κ κ′ κ″} {V′ W′ : Term Δᴿ}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
  → γ ⊢² $ κ ⊑ V′ ∶ p
  → γ ⊢² $ κ′ ⊑ W′ ∶ q
  → (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
  → Value V′
  → Value W′
  → δ op κ κ′ κ″
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ s ∈ applyTy keep (primResultTy op) ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ (primResultTy op) ]
      (V′ ⊕[ op ] W′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² $ κ″ ⊑ N′ ∶ s)
