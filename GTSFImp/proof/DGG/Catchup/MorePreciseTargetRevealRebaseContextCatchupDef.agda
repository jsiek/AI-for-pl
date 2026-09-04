{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePreciseTargetRevealRebaseContextCatchupDef where

-- File Charter:
--   * States target value catch-up at a focused CTI node beneath one
--     enclosing target reveal/source-rebase boundary.
--   * Returns the evolved root and focus derivations together with their
--     constructor-indexed zipper, so a later root simulation can resume
--     without a parallel world-frame stack.
--   * Keeps the enclosing reveal in the target term.  Discharging that reveal
--     remains the responsibility of target-reveal/rebase closing.
--   * Contains no catch-up proof or residual reduction-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _↑_)
open import Reduction using
  ( StoreChanges
  ; applyStore
  ; applyTys
  ; _—↠[_]_
  ) renaming ([] to []ˢ)
open import proof.Reduction using (applyReveals; applyVars)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  (RelatedConfiguration; pack; _↘ᶜ*_; TargetPathEvolution)
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePreciseTargetRevealRebaseContextCatchupᵀ : Set₁
MorePreciseTargetRevealRebaseContextCatchupᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᵖ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M L : Term Δᴸ} {M′ L′ : Term Δᴿ}
    {A C : Ty Δᴸ} {B B′ D Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → (root-related : γᵖ CTI.⊢² M ⊑ M′ ∶ p)
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
  → (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (path : pack root-related ↘ᶜ* pack focus-related)
  → Value L
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ M″ ∈ Term Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ γᵖ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ γᶠ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ p′ ∈ A ⊑ᵀ⟨ γᵖ′ ⟩ applyTys χsᴿ B ]
    Σ[ s′ ∈ C ⊑ᵀ⟨ γᶠ′ ⟩ applyTys χsᴿ D ]
      (M′ ↑ c′ —↠[ χsᴿ ] M″ ↑ applyReveals χsᴿ c′)
      × Value V′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × SourceRebaseᶜ γ′ γᵖ′ Xᴸ (applyVars χsᴿ Xᴿ)
      × Σ[ root-related′ ∈ γᵖ′ CTI.⊢² M ⊑ M″ ∶ p′ ]
        Σ[ focus-related′ ∈ γᶠ′ CTI.⊢² L ⊑ V′ ∶ s′ ]
          Σ[ path′ ∈ pack root-related′ ↘ᶜ* pack focus-related′ ]
            TargetPathEvolution path path′
