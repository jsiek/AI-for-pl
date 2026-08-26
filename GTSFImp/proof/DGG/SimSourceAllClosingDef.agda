{-# OPTIONS --safe #-}

module proof.DGG.SimSourceAllClosingDef where

-- File Charter:
--   * States source-universal closing against an arbitrary target term.
--   * Packages target catch-up and canonical world evolution for any
--     value-headed source type-application root step.
--   * Contains no source-universal closing proof or rule-specific adapter.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; ★; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⦂∀_[_])
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


SimSourceAllClosingᵀ : Set
SimSourceAllClosingᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² V ⊑ M′ ∶ p∀
  → (q : A ⊑ᵀ⟨ γ ⟩ ★)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ B)
  → Value V
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ s)
