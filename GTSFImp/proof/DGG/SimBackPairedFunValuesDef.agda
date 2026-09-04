{-# OPTIONS --safe #-}

module proof.DGG.SimBackPairedFunValuesDef where

-- File Charter:
--   * States the value-level inversion needed by backward simulation of a
--     paired function application.
--   * Given related function and argument values, turns one target root step
--     into the required source trace and canonical world evolution.
--   * Contains no catch-up phase and no value-inversion proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; blame; _·_; ⟨_,_,_⟩)
open import Reduction using
  (StoreChanges; applyStore; applyTy; applyTys; keep; _—→_; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPairedFunValuesᵀ : Set
SimBackPairedFunValuesᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V W : Term Δᴸ} {V′ W′ N′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ V′ ∶ ⇒⊑⇒ pA pB
  → γ ⊢² W ⊑ W′ ∶ pA
  → Value V
  → Value W
  → Value V′
  → Value W′
  → V′ · W′ —→ N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ N ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
        (V · W —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ q))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (V · W —↠[ χsᴸ ] blame))
