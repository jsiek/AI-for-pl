{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseContextPrimitiveValuesDef where

-- File Charter:
--   * States primitive-value simulation beneath one enclosing target
--     reveal/source-rebase boundary and an arbitrary CTI zipper context.
--   * Begins after both operands have caught up to values and owns the final
--     delta square plus target replay through the ready zipper.
--   * Keeps the public target-reveal/rebase closing conclusion inline.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using (Term; Value; ⟨_,_,_⟩; $; _⊕[_]_; _↑_)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import Primitives using (Const; Prim; primArgTy; primResultTy; δ)
open import Reduction using
  ( StoreChanges; applyStore; applyTy; applyTys; keep; _—↠[_]_ )
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimTargetRevealRebaseContextPrimitiveValuesᵀ : Set₁
SimTargetRevealRebaseContextPrimitiveValuesᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᵖ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source root-result : Term Δᴸ}
    {root-target L′ M′ : Term Δᴿ}
    {root-source-type : Ty Δᴸ}
    {root-target-type revealed-target-type : Ty Δᴿ}
    {representation : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {target-reveal : Conv↑ Δᴿ root-target-type revealed-target-type}
    {op : Prim} {κ κ′ κ″ : Const}
    {left-related : primArgTy op ⊑ᵀ⟨ γᶠ ⟩ primArgTy op}
    {right-related : primArgTy op ⊑ᵀ⟨ γᶠ ⟩ primArgTy op}
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
  → (left-related-term :
      γᶠ CTI.⊢² $ κ ⊑ L′ ∶ left-related)
  → (right-related-term :
      γᶠ CTI.⊢² $ κ′ ⊑ M′ ∶ right-related)
  → (result-related :
      primResultTy op ⊑ᵀ⟨ γᶠ ⟩ primResultTy op)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.⊕⊑⊕² op left-related-term right-related-term
        result-related))
  → TargetReady path
  → Value L′
  → Value M′
  → δ op κ κ′ κ″
  → RebuildSource path keep ($ κ″) root-result
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ result-target ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ final-related ∈
      applyTy keep root-source-type ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ revealed-target-type ]
      (root-target ↑ target-reveal —↠[ χsᴿ ] result-target)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)
