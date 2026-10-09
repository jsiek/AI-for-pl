{-# OPTIONS --safe #-}

module proof.DGG.Catchup.ContextualCatchupToMorePreciseDef where

-- File Charter:
--   * States target value catch-up at a focused CTI node beneath an arbitrary
--     whole-root CTI zipper.
--   * Returns evolved root and focus derivations with synchronized path
--     evolution, so application-right and primitive-right simulation can
--     install a ready target edge without broad sibling transport.
--   * Contains no catch-up proof or residual reduction-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; ⟨_,_,_⟩)
open import Reduction using
  ( StoreChanges; applyStore; applyTys; _—↠[_]_
  ) renaming ([] to []ˢ)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady
  ; TargetPathEvolution
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualCatchupToMorePreciseᵀ : Set₁
ContextualCatchupToMorePreciseᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source focus-source : Term Δᴸ}
    {root-target focus-target : Term Δᴿ}
    {root-source-type focus-source-type : Ty Δᴸ}
    {root-target-type focus-target-type : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {focus-type-related :
      focus-source-type ⊑ᵀ⟨ γᶠ ⟩ focus-target-type}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (focus-related :
      γᶠ CTI.⊢² focus-source ⊑ focus-target ∶ focus-type-related)
  → (path : pack root-related ↘ᶜ* pack focus-related)
  → TargetReady path
  → Value focus-source
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ root-target′ ∈ Term Δᴿ′ ]
    Σ[ focus-target′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ γᶠ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ root-type-related′ ∈
      root-source-type ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ root-target-type ]
    Σ[ focus-type-related′ ∈
      focus-source-type ⊑ᵀ⟨ γᶠ′ ⟩ applyTys χsᴿ focus-target-type ]
      (root-target —↠[ χsᴿ ] root-target′)
      × Value focus-target′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × Σ[ root-related′ ∈
          γ′ CTI.⊢² root-source ⊑ root-target′ ∶ root-type-related′ ]
        Σ[ focus-related′ ∈
          γᶠ′ CTI.⊢² focus-source ⊑ focus-target′ ∶
            focus-type-related′ ]
          Σ[ path′ ∈ pack root-related′ ↘ᶜ* pack focus-related′ ]
            TargetPathEvolution path path′
