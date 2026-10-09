{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimPairedCastValuesDef where

-- File Charter:
--   * States paired cast simulation beneath an arbitrary caller CTI context
--     after the target cast body has caught up to a related value.
--   * Keeps the rebuilt whole source and evolved whole target in the inline
--     conclusion because either cast may change its store.
--   * Contains no cast-reduction classifier or result wrapper.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
open import Consistency using (Env∼; _⊢_∼_)
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys
  ; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimPairedCastValuesᵀ : Set₁
ContextualSimPairedCastValuesᵀ = ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {root-source : Term Δᴸ}
    {root-result focus-result : Term Δᴸ′}
    {root-target target-value : Term Δᴿ}
    {root-source-type : Ty Δᴸ}
    {root-target-type : Ty Δᴿ}
    {source-value : Term Δᴸ}
    {source-type result-source-type : Ty Δᴸ}
    {target-type result-target-type : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
    {source-cast : μ ⊢ source-type ∼ result-source-type}
    {target-cast : μ′ ⊢ target-type ∼ result-target-type}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {value-type-related : source-type ⊑ᵀ⟨ γᶠ ⟩ target-type}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (value-related :
      γᶠ CTI.⊢² source-value ⊑ target-value ∶ value-type-related)
  → (result-type-related :
      result-source-type ⊑ᵀ⟨ γᶠ ⟩ result-target-type)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.cast⊑cast² source-cast target-cast value-related
        result-type-related))
  → TargetReady path
  → Value source-value
  → Value target-value
  → source-value ⟨ source-cast ⟩ —→[ χᴸ ] focus-result
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
        applyTys χsᴿ root-target-type ]
      (root-target —↠[ χsᴿ ] result-target)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)
