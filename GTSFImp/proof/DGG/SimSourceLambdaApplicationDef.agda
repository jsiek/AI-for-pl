{-# OPTIONS --safe #-}

module proof.DGG.SimSourceLambdaApplicationDef where

-- File Charter:
--   * States the lower induction for forward simulation when a source-only
--     type abstraction and a related target universal value are applied.
--   * Relates the source fresh reveal to the target root result while moving
--     from the source-only static scope to the runtime worlds of both steps.
--   * Exposes the resulting world, type-imprecision, evolution, and CTI
--     witnesses inline.

import Data.Fin as Fin
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using
  (Ty; TyCtx; NonVar; _∈ᵗ_; `∀; _[_]ᵗ; ⇑ᵗ)
open import TyStore using (TyStore)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; Λ_; _⦂∀_[_]; _↑_)
open import Reduction using
  (StoreChange; applyStore; applyTy; _—→[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimSourceLambdaApplicationᵀ : Set
SimSourceLambdaApplicationᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {V : Term (Nat.suc Δᴸ)} {V′ : Term Δᴿ}
    {N′ : Term Δᴿ′}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {p : C ⊑ᵀ⟨ liftLeftᶜ γ ⟩ `∀ C′}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → sourceRebaseCountᶜ γ ≡ 0
  → NonVar C
  → Fin.zero ∈ᵗ C
  → Value V
  → liftLeftᶜ γ ⊢² V ⊑ V′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value V′
  → V′ ⦂∀ C′ [ A′ ] —→[ χᴿ ] N′
  → Σ[ γ′ ∈
      ⟨ Nat.suc Δᴸ , applyStore (Reduction.bind A) Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
    Σ[ s ∈ ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩
        applyTy χᴿ (C′ [ A′ ]ᵗ) ]
      MultiWorldEvolution {W = γ} {W′ = γ′}
        (Reduction.bind A ∷ˢ []ˢ) (χᴿ ∷ˢ []ˢ)
      × (γ′ ⊢² V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ C 〗 ⊑ N′ ∶ s)
