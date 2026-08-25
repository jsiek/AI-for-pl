module proof.DGG.SimBackDef where

-- File Charter:
--   * States closed one-step backward simulation when the less precise right
--     term reduces.
--   * Uses complete endpoint contexts and canonical multi-world evolution.
--   * Requires directly that the outer world has no source rebase.
--   * Allows the more precise term to reach blame.
--   * Contains no simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; blame; ⟨_,_,_⟩)
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


SimBackᵀ : Set
SimBackᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStores χsᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ B ]
        (M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ q))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M —↠[ χsᴸ ] blame))
