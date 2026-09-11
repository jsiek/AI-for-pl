{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimBackPairedAllValuesDef where

-- File Charter:
--   * States backward paired-universal simulation beneath an arbitrary caller
--     CTI context after both universal heads have caught up to values.
--   * Rebuilds the whole target from the target type-application result and
--     returns the whole-root success or blame trace inline.
--   * Contains no paired-universal value proof or result wrapper.

import Data.Nat as Nat
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CastTerms using
  ( Term; Value; blame; ⟨_,_,_⟩; _⦂∀_[_]
  )
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; sourceTerm; targetTerm; _↘ᶜ*_
  )
open import proof.DGG.SimBackContextDef using (RebuildTarget; world)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


ContextualSimBackPairedAllValuesᵀ : Set₁
ContextualSimBackPairedAllValuesᵀ = ∀
    {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {root-source source-head : Term Δᴸ}
    {root-target target-head : Term Δᴿ}
    {focus-result root-target-result : Term Δᴿ′}
    {root-source-type : Ty Δᴸ}
    {root-target-type : Ty Δᴿ}
    {source-body : Ty (Nat.suc Δᴸ)}
    {source-argument : Ty Δᴸ}
    {target-body : Ty (Nat.suc Δᴿ)}
    {target-argument : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {universal-related :
      `∀ source-body ⊑ᵀ⟨ γᶠ ⟩ `∀ target-body}
  → openFramesᶜ γ ≡ []
  → (root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
  → (head-related :
      γᶠ CTI.⊢² source-head ⊑ target-head ∶
        universal-related)
  → (argument-related :
      source-argument ⊑ᵀ⟨ γᶠ ⟩ target-argument)
  → (result-related :
      source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γᶠ ⟩
        target-body [ target-argument ]ᵗ)
  → (path : pack root-related ↘ᶜ*
      pack (CTI.•⊑•² universal-related head-related
        argument-related result-related))
  → Value source-head
  → Value target-head
  → target-head ⦂∀ target-body [ target-argument ]
      —→[ χᴿ ] focus-result
  → RebuildTarget path χᴿ focus-result root-target-result
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ changesL ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        (⟨ Δᴸ′ , Σᴸ′ , [] ⟩)
        (⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩) ]
        (root-source —↠[ changesL ] sourceTerm root′)
        × targetTerm root′ ≡ root-target-result
        × MultiWorldEvolution
            {W = γ} {W′ = world root′}
            changesL (χᴿ ∷ˢ []ˢ) )
    ⊎ ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ changesL ∈ StoreChanges Δᴸ Δᴸ′ ]
        (root-source —↠[ changesL ] blame))
