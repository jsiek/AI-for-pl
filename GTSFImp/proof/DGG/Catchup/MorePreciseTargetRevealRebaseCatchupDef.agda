{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePreciseTargetRevealRebaseCatchupDef where

-- File Charter:
--   * States target-reveal catch-up across one source rebase.
--   * Isolates the case whose recursive CTI premise has nonzero source-rebase
--     count and therefore cannot use CatchupToMorePrecise recursively.
--   * Exposes the conversion typing and rebase evidence directly.
--   * Contains no catch-up proof or packaged result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _↑_)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePreciseTargetRevealRebaseCatchupᵀ : Set
MorePreciseTargetRevealRebaseCatchupᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {γᵖ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → γᵖ ⊢² V ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↑ c′ —↠[ χsᴿ ] V′)
      × Value V′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² V ⊑ V′ ∶ r)
