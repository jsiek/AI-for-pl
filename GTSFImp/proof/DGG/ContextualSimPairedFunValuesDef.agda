{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimPairedFunValuesDef where

-- File Charter:
--   * States paired-function value simulation beneath a caller CTI context
--     after both operands have caught up to target values.
--   * Keeps the whole root and its rebuilt source result in the conclusion,
--     because target evolution may change sibling evidence in the caller path.
--   * Contains no paired-function value proof or reduction-family classifier.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using (Term; Value; ⟨_,_,_⟩; _·_)
open import Imprecision using (⇒⊑⇒)
open import Reduction using
  ( StoreChanges; applyStore; applyTy; applyTys; keep; _—→_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimPairedFunValuesᵀ : Set₁
ContextualSimPairedFunValuesᵀ = ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source root-result focus-result : Term Δᴸ}
    {root-target L′ M′ : Term Δᴿ}
    {root-source-type : Ty Δᴸ}
    {root-target-type : Ty Δᴿ}
    {L M : Term Δᴸ}
    {argument-type result-type : Ty Δᴸ}
    {argument-type′ result-type′ : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {argument-related : argument-type ⊑ᵀ⟨ γᶠ ⟩ argument-type′}
    {result-related : result-type ⊑ᵀ⟨ γᶠ ⟩ result-type′}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (function-related :
      γᶠ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ argument-related result-related)
  → (argument-related-term :
      γᶠ CTI.⊢² M ⊑ M′ ∶ argument-related)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.·⊑·² function-related argument-related-term))
  → TargetReady path
  → Value L
  → Value M
  → Value L′
  → Value M′
  → L · M —→ focus-result
  → RebuildSource path keep focus-result root-result
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
