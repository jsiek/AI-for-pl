{-# OPTIONS --safe #-}

module proof.DGG.SimPairedFunValuesDef where

-- File Charter:
--   * States the value-level operation needed by forward simulation of a
--     paired function application.
--   * Given related function and argument values, turns one source root step
--     into the required target trace and canonical world evolution.
--   * Contains no catch-up phase and no value-inversion proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; _·_; ⟨_,_,_⟩)
open import Reduction using
  ( StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; keep
  ; _—→_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimPairedFunValuesᵀ : Set
SimPairedFunValuesᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V W N : Term Δᴸ} {V′ W′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² V ⊑ V′ ∶ ⇒⊑⇒ pA pB
  → γ ⊢² W ⊑ W′ ∶ pA
  → Value V
  → Value W
  → Value V′
  → Value W′
  → V · W —→ N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ applyTy keep B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (V′ · W′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ q)
