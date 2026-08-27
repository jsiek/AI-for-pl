{-# OPTIONS --safe #-}

module proof.DGG.SimPairedAllValuesDef where

-- File Charter:
--   * States the value-level operation needed by forward simulation of a
--     paired type application.
--   * Given related universal values, turns one source root step into the
--     matching target trace and canonical world evolution.
--   * Contains no target catch-up phase and no value-spine induction proof.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
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


SimPairedAllValuesᵀ : Set
SimPairedAllValuesᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵀ⟨ γ ⟩ `∀ C′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ V′ ∶ p∀
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Value V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (V′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ s)
