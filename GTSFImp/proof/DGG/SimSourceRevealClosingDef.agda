{-# OPTIONS --safe #-}

module proof.DGG.SimSourceRevealClosingDef where

-- File Charter:
--   * States the whole forward-simulation case for cancellation of a
--     source-only reveal.
--   * Exposes exactly the occupancy and representation evidence of the live
--     CTI constructor and returns evolution from its enclosing world.
--   * Contains no source-reveal simulation proof or catch-up wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx; TyVar; ★)
open import TyStore using (TyStore)
open import Consistency using (toRenameᵗ)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _↑_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (X⊑★)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimSourceRevealClosingᵀ : Set
SimSourceRevealClosingᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ 0
  → (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
  → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
  → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
  → γ ⊢² V ⊑ M′ ∶ p
  → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
  → Value V
  → V ↑ c —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ applyTy χᴸ A′ ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ r)
