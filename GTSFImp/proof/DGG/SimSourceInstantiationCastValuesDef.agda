{-# OPTIONS --safe #-}

module proof.DGG.SimSourceInstantiationCastValuesDef where

-- File Charter:
--   * States source-only beta-instantiation cast simulation for related
--     values.
--   * Isolates the separate induction through the source polymorphic value
--     spine and its source allocation.
--   * Exposes the evolved world and final CTI evidence directly.

open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_; instᵐ; inst_)
import Data.Fin as Fin
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
open import Reduction using
  ( applyStore
  ; applyTy
  ; bind
  ; _—→[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimSourceInstantiationCastValuesᵀ : Set
SimSourceInstantiationCastValuesᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term (suc Δᴸ)}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴸ} {C : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ zero∈A : Fin.zero ∈ᵗ A ⦄
    {B≠★ : B ≢ ★}
    {p : `∀ A ⊑ᵀ⟨ γ ⟩ C}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ V′ ∶ p
  → (q : B ⊑ᵀ⟨ γ ⟩ C)
  → Value V
  → Value V′
  → V ⟨ (inst c) B≠★ ⟩ —→[ bind ★ ] N
  → Σ[ γ′ ∈
      ⟨ suc Δᴸ , applyStore (bind ★) Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , [] ⟩ ]
    Σ[ r ∈ applyTy (bind ★) B ⊑ᵀ⟨ γ′ ⟩ C ]
      MultiWorldEvolution
        {W = γ} {W′ = γ′} ((bind ★) ∷ˢ []ˢ) []ˢ
      × (γ′ ⊢² N ⊑ V′ ∶ r)
