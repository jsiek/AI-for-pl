{-# OPTIONS --safe #-}

module proof.DGG.SimPairedFunClosingDef where

-- File Charter:
--   * States simulation of a paired source/target application when both
--     source operands are values and the source application takes a root
--     step.
--   * Packages target function and argument catch-up behind one
--     source-rule-independent interface.
--   * Contains no paired function-closing proof or rule-specific adapter.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _·_)
open import Reduction using
  ( StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; keep
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimPairedFunClosingᵀ : Set
SimPairedFunClosingᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {L M N : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → γ ⊢² M ⊑ M′ ∶ pA
  → Value L
  → Value M
  → L · M —→[ keep ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ applyTy keep B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (L′ · M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ q)
