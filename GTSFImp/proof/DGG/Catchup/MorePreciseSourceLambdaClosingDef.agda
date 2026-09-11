{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseSourceLambdaClosingDef where

-- File Charter:
--   * States source-only type-abstraction closing after target catch-up has
--     completed beneath the protected left type scope.
--   * Pulls target-only world evolution back out of that scope and rebuilds
--     the source type abstraction at the resulting base world.
--   * Isolates the separate induction that normalizes chronological target
--     allocations against the canonical left-lifted CTI premise.
--   * Contains no target reduction, catch-up proof, or packaged result wrapper.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; `∀)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; ⇑ᵉᵗ; Λ_)
open import Reduction using (StoreChanges; applyTys)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePreciseSourceLambdaClosingᵀ : Set
MorePreciseSourceLambdaClosingᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {γᵇ : ⇑ᵉᵗ ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {V : Term (suc Δᴸ)} {V′ : Term Δᴿ′}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵀ⟨ γᵇ ⟩ applyTys χsᴿ B}
  → openFramesᶜ γ ≡ []
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → MultiWorldEvolution {W = liftLeftᶜ γ} {W′ = γᵇ} []ˢ χsᴿ
  → γᵇ ⊢² V ⊑ V′ ∶ p
  → (q : `∀ A ⊑ᵀ⟨ γ ⟩ B)
  → Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ `∀ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² Λ V ⊑ V′ ∶ r)
