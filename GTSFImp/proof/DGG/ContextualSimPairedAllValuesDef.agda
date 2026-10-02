{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimPairedAllValuesDef where

-- File Charter:
--   * States paired type-application value simulation beneath an arbitrary
--     caller CTI context after the target head has caught up to a value.
--   * Keeps the whole root and rebuilt source result in the inline conclusion,
--     because target evolution may change sibling evidence in the caller path.
--   * Contains no universal-value proof or reduction-family classifier.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⦂∀_[_])
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys
  ; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; _↘ᶜ*_; TargetReady; RebuildSource )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimPairedAllValuesᵀ : Set₁
ContextualSimPairedAllValuesᵀ = ∀
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
    {source-body : Ty (Nat.suc Δᴸ)} {source-argument : Ty Δᴸ}
    {target-body : Ty (Nat.suc Δᴿ)} {target-argument : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {universal-related :
      `∀ source-body ⊑ᵀ⟨ γᶠ ⟩ `∀ target-body}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (value-related :
      γᶠ CTI.⊢² source-value ⊑ target-value ∶ universal-related)
  → (argument-related :
      source-argument ⊑ᵀ⟨ γᶠ ⟩ target-argument)
  → (result-related :
      source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γᶠ ⟩
        target-body [ target-argument ]ᵗ)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.•⊑•² universal-related value-related
        argument-related result-related))
  → TargetReady path
  → Value source-value
  → Value target-value
  → source-value ⦂∀ source-body [ source-argument ]
      —→[ χᴸ ] focus-result
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
