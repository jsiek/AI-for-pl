{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimBackPrimitiveValuesDef where

-- File Charter:
--   * States backward primitive-value simulation beneath an arbitrary caller
--     CTI context after both source operands have caught up to values.
--   * Rebuilds the whole target from the target delta result and returns the
--     whole-root success or blame trace inline.
--   * Contains no primitive-value proof or result wrapper.

open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using
  ( Term; Value; blame; ⟨_,_,_⟩; $; _⊕[_]_
  )
open import Primitives using (Const; Prim; primArgTy; primResultTy; δ)
open import Reduction using
  ( StoreChanges; applyStore; keep; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; sourceTerm; targetTerm; _↘ᶜ*_
  )
open import proof.DGG.SimBackContextDef using (RebuildTarget; world)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimBackPrimitiveValuesᵀ : Set₁
ContextualSimBackPrimitiveValuesᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source source-left source-right : Term Δᴸ}
    {root-target root-target-result : Term Δᴿ}
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
      γᶠ CTI.⊢² source-left ⊑ $ κ ∶ left-type-related)
  → (right-related :
      γᶠ CTI.⊢² source-right ⊑ $ κ′ ∶ right-type-related)
  → (result-type-related :
      primResultTy op ⊑ᵀ⟨ γᶠ ⟩ primResultTy op)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.⊕⊑⊕² op left-related right-related
        result-type-related))
  → Value source-left
  → Value source-right
  → δ op κ κ′ κ″
  → RebuildTarget path keep ($ κ″) root-target-result
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ changesL ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        (⟨ Δᴸ′ , Σᴸ′ , [] ⟩)
        (⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩) ]
        (root-source —↠[ changesL ] sourceTerm root′)
        × targetTerm root′ ≡ root-target-result
        × MultiWorldEvolution
            {W = γ} {W′ = world root′}
            changesL (keep ∷ˢ []ˢ) )
    ⊎ ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ changesL ∈ StoreChanges Δᴸ Δᴸ′ ]
        (root-source —↠[ changesL ] blame))
