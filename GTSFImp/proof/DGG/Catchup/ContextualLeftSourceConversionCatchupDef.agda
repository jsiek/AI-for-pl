{-# OPTIONS --safe #-}

module proof.DGG.Catchup.ContextualLeftSourceConversionCatchupDef where

-- File Charter:
--   * States source-reveal catch-up beneath the canonical full CTI zipper
--     as a separate semantic induction.
--   * Keeps the exact reveal checkpoint and whole related root visible while
--     returning the evolved root-to-focus path inline.
--   * Contains no catch-up proof, classifier, or packaged result wrapper.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Conversion using (Conv↑)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _↑_)
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


ContextualLeftSourceRevealCatchupAt : ℕ → Set₁
ContextualLeftSourceRevealCatchupAt fuel = ∀
    {Δᴸ Δᴿ : TyCtx} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {root-source : Term Δᴸ} {root-target : Term Δᴿ}
    {root-source-type : Ty Δᴸ} {root-target-type : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {c : Conv↑ Δᴸ A A′} {p : A′ ⊑ᵀ⟨ γᶠ ⟩ B}
    {related : γᶠ CTI.⊢² M ↑ c ⊑ V′ ∶ p}
    {root-related :
      γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related}
  → openFramesᶜ γ ≡ []
  → (path : pack root-related ↘ᶜ* pack related)
  → Value V′
  → SourceCastBound fuel related
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
