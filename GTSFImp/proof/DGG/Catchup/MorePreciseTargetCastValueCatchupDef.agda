{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePreciseTargetCastValueCatchupDef where

-- File Charter:
--   * States catch-up for one target consistency cast whose body is already
--     a value related to a source value.
--   * Covers both target-only and paired cast CTI rules through their direct
--     framed relation, without classifying those rules in the interface.
--   * Isolates the separate induction on consistency-cast reduction.
--   * Contains no catch-up proof or packaged result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePreciseTargetCastValueCatchupᵀ : Set
MorePreciseTargetCastValueCatchupᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν′ : Env∼ Δᴿ}
    {c′ : ν′ ⊢ B ∼ B′} {p : A ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² V ⊑ V′ ⟨ c′ ⟩ ∶ p
  → Value V
  → Value V′
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ W′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] W′)
      × Value W′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² V ⊑ W′ ∶ q)
