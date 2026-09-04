{-# OPTIONS --safe #-}

module proof.DGG.SimPairedRevealClosingDef where

-- File Charter:
--   * States the whole forward-simulation case for cancellation of paired
--     reveals.
--   * Exposes generator representations and structural-position agreement
--     directly, without a residual or catch-up wrapper.
--   * Contains no paired-reveal simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar)
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
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimPairedRevealClosingᵀ : Set
SimPairedRevealClosingᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
    {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    {p : A ⊑ᵀ⟨ γ ⟩ A′}
  → openFramesᶜ γ ≡ []
  → (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
  → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
  → γ ⊢² V ⊑ M′ ∶ p
  → (q : B ⊑ᵀ⟨ γ ⟩ B′)
  → Value V
  → V ↑ c —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↑ c′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ r)
