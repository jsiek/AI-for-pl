{-# OPTIONS --safe #-}

module proof.DGG.SimBackSourceLambdaDef where

-- File Charter:
--   * States the source-only type-abstraction case of backward simulation.
--   * Exposes the exact canonical CTI rule evidence and repeats the complete
--     SimBack conclusion without a result wrapper.
--   * Is separated because the recursive relation lives under a left-lifted
--     world while the source type abstraction itself cannot reduce.
--   * Contains no source-lambda simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; `∀)
open import TyStore using (TyStore)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _⊢_⦂_; Λ_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackSourceLambdaᵀ : Set
SimBackSourceLambdaᵀ = ∀ {Deltaᴸ Deltaᴿ Deltaᴿ′ : TyCtx}
    {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
    {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {V : Term (suc Deltaᴸ)} {M′ : Term Deltaᴿ} {N′ : Term Deltaᴿ′}
    {A : Ty (suc Deltaᴸ)} {B : Ty Deltaᴿ}
    {p : A ⊑ᵀ⟨ γ ▻ᶜ lift-left-changeᶜ refl ⟩ B}
    {χᴿ : StoreChange Deltaᴿ Deltaᴿ′}
  → openFramesᶜ γ ≡ []
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → ⟨ Deltaᴿ , Σᴿ , [] ⟩ ⊢ M′ ⦂ B
  → (γ ▻ᶜ lift-left-changeᶜ refl) ⊢² V ⊑ M′ ∶ p
  → (q : `∀ A ⊑ᵀ⟨ γ ⟩ B)
  → M′ —→[ χᴿ ] N′
  → ( Σ[ Deltaᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Deltaᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
      Σ[ N ∈ Term Deltaᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Deltaᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Deltaᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ (`∀ A) ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ B ]
        (Λ V —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Deltaᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
        (Λ V —↠[ χsᴸ ] blame))
