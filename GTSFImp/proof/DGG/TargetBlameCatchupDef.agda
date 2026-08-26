{-# OPTIONS --safe #-}

module proof.DGG.TargetBlameCatchupDef where

-- File Charter:
--   * States source catch-up when the less precise target is blame.
--   * Returns exactly the source reduction to blame needed by backward
--     simulation and the top-level dynamic gradual guarantee.
--   * Contains no catch-up proof or world-compatibility wrapper.

open import Data.List using ([])
open import Data.Product using (Σ-syntax)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; blame; ⟨_,_,_⟩)
open import Reduction using (StoreChanges; _—↠[_]_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


TargetBlameCatchupᵀ : Set
TargetBlameCatchupᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ blame ∶ p
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      (M —↠[ χsᴸ ] blame)
