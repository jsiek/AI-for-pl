{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseContextSourceAllValuesDef where

-- File Charter:
--   * States source-only type-application value simulation beneath one
--     enclosing target reveal/source-rebase boundary and a CTI zipper.
--   * Begins after the related heads are values; its Proof owns the five
--     source universal roots and replays the silent target trace through the
--     synchronized ready path.
--   * Keeps the public target-reveal/rebase closing conclusion inline.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⦂∀_[_]; _↑_)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys
  ; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx; TyVar; ★; `∀; _[_]ᵗ)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimTargetRevealRebaseContextSourceAllValuesᵀ : Set₁
SimTargetRevealRebaseContextSourceAllValuesᵀ = ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᵖ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {root-source : Term Δᴸ}
    {root-result focus-result : Term Δᴸ′}
    {root-target V′ : Term Δᴿ}
    {root-source-type : Ty Δᴸ}
    {root-target-type revealed-target-type : Ty Δᴿ}
    {representation : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {target-reveal : Conv↑ Δᴿ root-target-type revealed-target-type}
    {V : Term Δᴸ}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {universal-related : `∀ C ⊑ᵀ⟨ γᶠ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (target-reveal⊢ :
      Σᴿ ⊢↑[ Xᴿ ⦂ representation ] target-reveal)
  → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
  → {root-related-type :
      root-source-type ⊑ᵀ⟨ γᵖ ⟩ root-target-type}
  → (root-related :
      γᵖ CTI.⊢² root-source ⊑ root-target ∶ root-related-type)
  → (revealed-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ revealed-target-type)
  → (related : γᶠ CTI.⊢² V ⊑ V′ ∶ universal-related)
  → (argument-related : A ⊑ᵀ⟨ γᶠ ⟩ ★)
  → (result-related : C [ A ]ᵗ ⊑ᵀ⟨ γᶠ ⟩ B)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.•⊑² universal-related related argument-related
        result-related))
  → TargetReady path
  → Value V
  → Value V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] focus-result
  → RebuildSource path χᴸ focus-result root-result
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ result-target ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ final-related ∈
      applyTy χᴸ root-source-type ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ revealed-target-type ]
      (root-target ↑ target-reveal —↠[ χsᴿ ] result-target)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)
