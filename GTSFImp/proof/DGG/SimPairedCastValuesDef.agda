{-# OPTIONS --safe #-}

module proof.DGG.SimPairedCastValuesDef where

-- File Charter:
--   * States simulation of a paired ordinary cast after both cast bodies
--     have reached related values.
--   * Packages all value/value cast-root combinations behind one interface.
--   * Does not perform the initial target catch-up or split by cast rule.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
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


SimPairedCastValuesᵀ : Set
SimPairedCastValuesᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
    {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
    {p : A ⊑ᵀ⟨ γ ⟩ A′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ V′ ∶ p
  → (q : B ⊑ᵀ⟨ γ ⟩ B′)
  → Value V
  → Value V′
  → V ⟨ c ⟩ —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ r)
