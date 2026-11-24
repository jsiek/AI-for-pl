{-# OPTIONS --safe #-}

module proof.DGG.Catchup.ContextualLeftSourceTypeAppCatchupDef where

-- File Charter:
--   * States source type-application catch-up beneath the canonical full
--     CTI zipper as a separate semantic induction.
--   * Keeps the exact source type-application checkpoint and whole related
--     root visible while returning the evolved root-to-focus path inline.
--   * Contains no catch-up proof, classifier, or packaged result wrapper.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; ★; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩)
open import Reduction using (StoreChanges; _—↠[_]_)
  renaming ([] to []ˢ)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.LeftValueCatchupDef using
  (SourceCastBound)
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; sourceTerm; targetTerm; _↘ᶜ*_
  )
open import proof.DGG.SimBackContextDef using
  (world; SourcePathEvolution)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution)


ContextualLeftSourceTypeAppCatchupAt : ℕ → Set₁
ContextualLeftSourceTypeAppCatchupAt fuel = ∀
    {Δᴸ Δᴿ : TyCtx} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source : Term Δᴸ} {root-target : Term Δᴿ}
    {root-source-type : Ty Δᴸ} {root-target-type : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {C : Ty (suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : (`∀ C) ⊑ᵀ⟨ γᶠ ⟩ B}
    {related : γᶠ CTI.⊢² M ⊑ V′ ∶ p∀}
    {q : A ⊑ᵀ⟨ γᶠ ⟩ ★}
    {r : C [ A ]ᵗ ⊑ᵀ⟨ γᶠ ⟩ B}
    {root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related}
  → openFramesᶜ γ ≡ []
  → (path : pack root-related ↘ᶜ*
      pack (CTI.•⊑² p∀ related q r))
  → Value V′
  → SourceCastBound fuel (CTI.•⊑² p∀ related q r)
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ focus′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ path′ ∈ root′ ↘ᶜ* focus′ ]
        (root-source —↠[ χsᴸ ] sourceTerm root′)
        × Value (sourceTerm focus′)
        × targetTerm root′ ≡ root-target
        × targetTerm focus′ ≡ V′
        × SourcePathEvolution path path′
        × MultiWorldEvolution
            {W = γ} {W′ = world root′} χsᴸ []ˢ)
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (root-source —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)
