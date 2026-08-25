module proof.DGG.MultiSimDef where

-- File Charter:
--   * States closed multi-step simulation when the more precise left term
--     reduces.
--   * Uses complete endpoint contexts and canonical multi-world evolution.
--   * Requires directly that the outer world has no source rebase.
--   * Contains no simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; ⟨_,_,_⟩)
open import Reduction using
  (StoreChanges; applyStores; applyTys; _—↠[_]_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


Sim*ᵀ : Set
Sim*ᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² M ⊑ M′ ∶ p
  → M —↠[ χsᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStores χsᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , applyStores χsᴿ Σᴿ , [] ⟩ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ q)
