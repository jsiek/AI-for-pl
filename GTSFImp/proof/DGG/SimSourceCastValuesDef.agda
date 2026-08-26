{-# OPTIONS --safe #-}

module proof.DGG.SimSourceCastValuesDef where

-- File Charter:
--   * States simulation of a source-only ordinary cast after its target body
--     has caught up to a related value.
--   * Keeps that target value and its store fixed while the source cast closes.
--   * Packages all value/value source-cast roots behind one interface.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
open import Reduction using
  ( StoreChange
  ; applyStore
  ; applyTy
  ; _—→[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimSourceCastValuesᵀ : Set
SimSourceCastValuesᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {C : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {c : μ ⊢ A ∼ B}
    {p : A ⊑ᵀ⟨ γ ⟩ C}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² V ⊑ V′ ∶ p
  → (q : B ⊑ᵀ⟨ γ ⟩ C)
  → Value V
  → Value V′
  → V ⟨ c ⟩ —→[ χᴸ ] N
  → Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , [] ⟩ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ C ]
      MultiWorldEvolution
        {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) []ˢ
      × (γ′ ⊢² N ⊑ V′ ∶ r)
