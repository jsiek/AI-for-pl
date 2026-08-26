{-# OPTIONS --safe #-}

module proof.DGG.SimPrimitiveClosingDef where

-- File Charter:
--   * States the whole forward-simulation case for a primitive delta step.
--   * Includes the two target value catch-ups and the final primitive square
--     in one separate induction interface.
--   * Contains no primitive simulation proof or catch-up result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (TyCtx)
open import TyStore using (TyStore)
open import Primitives using (primArgTy; primResultTy; δ)
open import CastTerms using (Term; ⟨_,_,_⟩; $; _⊕[_]_)
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


SimPrimitiveClosingᵀ : Set
SimPrimitiveClosingᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {op κ κ′ κ″} {L′ M′ : Term Δᴿ}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² $ κ ⊑ L′ ∶ p
  → γ ⊢² $ κ′ ⊑ M′ ∶ q
  → (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
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
      (L′ ⊕[ op ] M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² $ κ″ ⊑ N′ ∶ s)
