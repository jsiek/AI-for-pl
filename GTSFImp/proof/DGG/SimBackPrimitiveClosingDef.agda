{-# OPTIONS --safe #-}

module proof.DGG.SimBackPrimitiveClosingDef where

-- File Charter:
--   * States backward simulation for a target primitive delta root.
--   * Exposes both operand relations and the delta proof directly.
--   * Contains no primitive-closing proof or result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (TyCtx)
open import TyStore using (TyStore)
open import Primitives using (primArgTy; primResultTy; δ)
open import CastTerms using (Term; blame; $; _⊕[_]_; ⟨_,_,_⟩)
open import Reduction using
  (StoreChanges; applyStore; applyTy; applyTys; keep; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPrimitiveClosingᵀ : Set
SimBackPrimitiveClosingᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {op κ κ′ κ″} {L M : Term Δᴸ}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
  → openFramesᶜ γ ≡ []
  → γ ⊢² L ⊑ $ κ ∶ p
  → γ ⊢² M ⊑ $ κ′ ∶ q
  → (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
  → δ op κ κ′ κ″
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ s ∈ applyTys χsᴸ (primResultTy op) ⊑ᵀ⟨ γ′ ⟩
          applyTy keep (primResultTy op) ]
        (L ⊕[ op ] M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ $ κ″ ∶ s))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (L ⊕[ op ] M —↠[ χsᴸ ] blame))
