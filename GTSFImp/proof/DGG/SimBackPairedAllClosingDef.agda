{-# OPTIONS --safe #-}

module proof.DGG.SimBackPairedAllClosingDef where

-- File Charter:
--   * States backward simulation for a paired type application whose target
--     operator is a value and takes a root step.
--   * Covers pure and allocating universal root reductions without a root
--     classifier or residual family.
--   * Contains no paired universal-closing proof.

import Data.Nat as Nat
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; blame; _⦂∀_[_]; ⟨_,_,_⟩)
open import Reduction using
  (StoreChange; StoreChanges; applyStore; applyTy; applyTys;
   _—→[_]_; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPairedAllClosingᵀ : Set
SimBackPairedAllClosingᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵀ⟨ γ ⟩ `∀ C′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² M ⊑ M′ ∶ p∀
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value M′
  → M′ ⦂∀ C′ [ A′ ] —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ s ∈ applyTys χsᴸ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩
          applyTy χᴿ (C′ [ A′ ]ᵗ) ]
        (M ⦂∀ C [ A ] —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ s))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M ⦂∀ C [ A ] —↠[ χsᴸ ] blame))
