{-# OPTIONS --safe #-}

module proof.DGG.SimBackCastClosingDef where

-- File Charter:
--   * States backward simulation for paired and target-only ordinary casts
--     whose target payload is a value and takes a root cast step.
--   * Covers pure cast roots and allocating instantiation without a step
--     classifier or residual family.
--   * Contains no cast-closing proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; blame; _⟨_⟩; ⟨_,_,_⟩)
open import Reduction using
  (StoreChange; StoreChanges; applyStore; applyTy; applyTys;
   _—→[_]_; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPairedCastClosingᵀ : Set
SimBackPairedCastClosingᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {C A : Ty Δᴸ} {C′ A′ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {p : C ⊑ᵀ⟨ γ ⟩ C′}
  → openFramesᶜ γ ≡ []
  → (c : μᴸ ⊢ C ∼ A)
  → (c′ : μᴿ ⊢ C′ ∼ A′)
  → γ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → Value M′
  → M′ ⟨ c′ ⟩ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ A′ ]
        (M ⟨ c ⟩ —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M ⟨ c ⟩ —↠[ χsᴸ ] blame))


SimBackTargetCastClosingᵀ : Set
SimBackTargetCastClosingᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {μᴿ : Env∼ Δᴿ}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (c′ : μᴿ ⊢ B ∼ B′)
  → γ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Value M′
  → M′ ⟨ c′ ⟩ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ B′ ]
        (M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M —↠[ χsᴸ ] blame))
