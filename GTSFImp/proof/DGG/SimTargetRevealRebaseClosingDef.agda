{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseClosingDef where

-- File Charter:
--   * States forward simulation beneath the target reveal that closes a
--     source-rebase scope.
--   * Exposes exactly the current CTI rebase evidence and returns evolution
--     from the enclosing world.
--   * Contains no source-rebase simulation proof or generic frame wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar; ＇_)
open import TyStore using (TyStore; lookupStore)
open import Consistency using (toRenameᵗ)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import CastTerms using (Term; ⟨_,_,_⟩; _↑_)
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


SimTargetRevealRebaseClosingᵀ : Set
SimTargetRevealRebaseClosingᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
  → {p : A ⊑ᵀ⟨
      γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B}
  → (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented)
      ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↑ c′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ ⊢² N ⊑ N′ ∶ r)
