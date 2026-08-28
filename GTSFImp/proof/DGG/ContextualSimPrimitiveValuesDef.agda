{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimPrimitiveValuesDef where

-- File Charter:
--   * States primitive-value simulation beneath an arbitrary caller CTI
--     context after both target operands have caught up to values.
--   * Keeps the whole root and rebuilt source result in the inline conclusion,
--     because target evolution may change sibling evidence in the caller path.
--   * Contains no primitive-value proof or reduction-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using (Term; Value; ⟨_,_,_⟩; $; _⊕[_]_)
open import Primitives using (Const; Prim; primArgTy; primResultTy; δ)
open import Reduction using
  ( StoreChanges; applyStore; applyTy; applyTys; keep; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimPrimitiveValuesᵀ : Set₁
ContextualSimPrimitiveValuesᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source root-result : Term Δᴸ}
    {root-target left-target right-target : Term Δᴿ}
    {root-source-type : Ty Δᴸ}
    {root-target-type : Ty Δᴿ}
    {op : Prim} {κ κ′ κ″ : Const}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {left-type-related :
      primArgTy op ⊑ᵀ⟨ γᶠ ⟩ primArgTy op}
    {right-type-related :
      primArgTy op ⊑ᵀ⟨ γᶠ ⟩ primArgTy op}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (left-related :
      γᶠ CTI.⊢² $ κ ⊑ left-target ∶ left-type-related)
  → (right-related :
      γᶠ CTI.⊢² $ κ′ ⊑ right-target ∶ right-type-related)
  → (result-type-related :
      primResultTy op ⊑ᵀ⟨ γᶠ ⟩ primResultTy op)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.⊕⊑⊕² op left-related right-related
        result-type-related))
  → TargetReady path
  → Value left-target
  → Value right-target
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
        applyTys χsᴿ root-target-type ]
      (root-target —↠[ χsᴿ ] result-target)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (keep ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)
