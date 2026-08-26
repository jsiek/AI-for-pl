{-# OPTIONS --safe #-}

module proof.DGG.SimBackPairedFunClosingDef where

-- File Charter:
--   * States backward simulation for a paired application whose target takes
--     a pure root step.
--   * Exposes the two premise relations and the root reduction directly.
--   * Contains no application-closing proof or root classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; blame; _·_; ⟨_,_,_⟩)
open import Imprecision using (⇒⊑⇒)
open import Reduction using
  (StoreChanges; applyStore; applyTy; applyTys; keep; _—→_; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPairedFunClosingᵀ : Set
SimBackPairedFunClosingᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {L M : Term Δᴸ} {L′ M′ N′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → γ ⊢² M ⊑ M′ ∶ pA
  → Value L′
  → Value M′
  → L′ · M′ —→ N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
        (L · M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ q))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (L · M —↠[ χsᴸ ] blame))
