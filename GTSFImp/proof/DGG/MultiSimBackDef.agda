module proof.DGG.MultiSimBackDef where

-- File Charter:
--   * States closed multi-step backward simulation when the less precise
--     right term reduces.
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
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
open import proof.Reduction using (_++χ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBack*ᵀ : Set
SimBack*ᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² M ⊑ M′ ∶ p
  → M′ —↠[ χsᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ Δᴿ″ ∈ TyCtx ]
      Σ[ Σᴿ″ ∈ TyStore Δᴿ″ ]
      Σ[ ψsᴿ ∈ StoreChanges Δᴿ′ Δᴿ″ ]
      Σ[ N₂′ ∈ Term Δᴿ″ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ″ , Σᴿ″ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩
          applyTys ψsᴿ (applyTys χsᴿ B) ]
        (M —↠[ χsᴸ ] N)
        × (N′ —↠[ ψsᴿ ] N₂′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χsᴿ ++χ ψsᴿ)
        × (γ′ ⊢² N ⊑ N₂′ ∶ q))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M —↠[ χsᴸ ] blame))
