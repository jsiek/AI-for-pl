module proof.DGG.SimDef where

-- File Charter:
--   * States closed one-step simulation when the more precise left term
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
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyStores
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


Simᵀ : Set
Simᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² M ⊑ M′ ∶ p
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , applyStores χsᴿ Σᴿ , [] ⟩ ]
    Σ[ q ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ q)
