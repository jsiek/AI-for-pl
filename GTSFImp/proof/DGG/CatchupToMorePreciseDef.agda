{-# OPTIONS --safe #-}

module proof.DGG.CatchupToMorePreciseDef where

-- File Charter:
--   * States right-side value catch-up for a source value related to an
--     arbitrary target term.
--   * The more precise target reaches a related value; there is no target
--     blame alternative in the forward-simulation direction.
--   * Evolves only the target context using canonical multi-world evolution.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


CatchupToMorePrecise : Set
CatchupToMorePrecise = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ M′ ∶ p
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] V′)
      × Value V′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² V ⊑ V′ ∶ q)
