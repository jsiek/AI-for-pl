{-# OPTIONS --safe #-}

module proof.DGG.SourcePathBlameLemma where

-- File Charter:
--   * Lifts a focused source reduction to blame through every edge of the
--     canonical full-context CTI zipper.
--   * Replays the administrative source keep steps on any accompanying world
--     evolution without changing its final world.
--   * Exports the zero-step specialization used by contextual source catch-up.

open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; sym)

open import CastTerms using (Ctx; Δᵉ; Term; blame; ⟨_,_,_⟩)
open import TermCtx using (TermCtx)
open import Types using (TyCtx)
open import TyStore using (TyStore)
import Reduction
open import Reduction using
  ( StoreChanges; applyTerms; keep; pure-step
  ; blame-·₁; blame-⊕₁; _—↠[_]_; ↠-refl; ↠-step
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.Reduction using
  ( _++χ_; appL-↠; appR-blame-↠; primL-↠; primR-↠
  ; typeApp-blame-↠; cast-blame-↠; reveal-blame-↠
  ; conceal-blame-↠; composeReduction
  ; applyTerms-preserves-Value
  )
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.World using (_⊑ᶜ_)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; append-left-keep; evolutions-refl )


source-path-blame-after : ∀ {Cᴸ Cᴿ : Ctx}
    {root focus : RelatedConfiguration Cᴸ Cᴿ}
    {Δᴸ′ : TyCtx} {changesL : StoreChanges (Δᵉ Cᴸ) Δᴸ′}
  → (path : root ↘ᶜ* focus)
  → sourceTerm focus —↠[ changesL ] blame
  → Σ[ changesL′ ∈ StoreChanges (Δᵉ Cᴸ) Δᴸ′ ]
      (sourceTerm root —↠[ changesL′ ] blame)
      × (∀ {Σᴸ′ : TyStore Δᴸ′} {Γᴸ′ : TermCtx Δᴸ′}
          {Cᴿ′ : Ctx} {W : Cᴸ ⊑ᶜ Cᴿ}
          {W′ : ⟨ Δᴸ′ , Σᴸ′ , Γᴸ′ ⟩ ⊑ᶜ Cᴿ′}
          {changesR : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
        → MultiWorldEvolution
            {W = W} {W′ = W′} changesL changesR
        → MultiWorldEvolution
            {W = W} {W′ = W′} changesL′ changesR)
source-path-blame-after focus-here focus-steps =
  _ , focus-steps , (λ evolution → evolution)
source-path-blame-after
    (focus-there
      (focus-·₁ {M = M} function-related argument-related) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-·₁ {M = M} function-related argument-related) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) ,
    composeReduction (appL-↠ inner-steps)
      (↠-step (pure-step blame-·₁) ↠-refl) ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-·₂ function-related argument-related source-value) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-·₂ function-related argument-related source-value) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) ,
    appR-blame-↠ source-value inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-⊕₁ {M = M} left-related right-related result-related) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-⊕₁ {M = M} left-related right-related result-related) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) ,
    composeReduction (primL-↠ inner-steps)
      (↠-step (pure-step blame-⊕₁) ↠-refl) ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-⊕₂ left-related right-related result-related source-value)
      tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-⊕₂ left-related right-related result-related source-value)
      tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) ,
    composeReduction (primR-↠ source-value inner-steps)
      (↠-step
        (pure-step
          (Reduction.blame-⊕₂
            (applyTerms-preserves-Value changesL source-value)))
        ↠-refl) ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there (focus-•-paired p∀ related q r) tail) focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there (focus-•-paired p∀ related q r) tail) focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , typeApp-blame-↠ inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there (focus-•-source p∀ related q r) tail) focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there (focus-•-source p∀ related q r) tail) focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , typeApp-blame-↠ inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there (focus-cast-paired c c′ related q) tail) focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there (focus-cast-paired c c′ related q) tail) focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , cast-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there (focus-cast-target c′ related q) tail) focus-steps =
  source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there (focus-cast-source c related q) tail) focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there (focus-cast-source c related q) tail) focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , cast-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-target-reveal-identity c′⊢ absent related q) tail)
    focus-steps =
  source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-target-conceal-identity c′⊢ absent related q) tail)
    focus-steps =
  source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-source-reveal-identity {c = c} c⊢ absent related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-source-reveal-identity {c = c} c⊢ absent related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-source-conceal-identity {c = c} c⊢ absent related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-source-conceal-identity {c = c} c⊢ absent related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-source-reveal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-source-reveal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-source-conceal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-source-conceal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-reveal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-reveal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-conceal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-steps
    with source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-conceal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-steps
  | changesL , inner-steps , evolve =
    changesL ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    (λ evolution → append-left-keep (evolve evolution))
source-path-blame-after
    (focus-there
      (focus-target-reveal-rebase c′⊢ rebase related q) tail)
    focus-steps =
  source-path-blame-after tail focus-steps
source-path-blame-after
    (focus-there
      (focus-target-conceal-rebase c′⊢ rebase related q) tail)
    focus-steps =
  source-path-blame-after tail focus-steps


source-path-blame : ∀ {Cᴸ Cᴿ : Ctx} {W : Cᴸ ⊑ᶜ Cᴿ}
    {root focus : RelatedConfiguration Cᴸ Cᴿ}
  → (path : root ↘ᶜ* focus)
  → sourceTerm focus ≡ blame
  → Σ[ changesL ∈ StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ) ]
      (sourceTerm root —↠[ changesL ] blame)
      × MultiWorldEvolution {W = W} {W′ = W} changesL []ˢ
source-path-blame {W = W} path focus-blame
    with source-path-blame-after path
      (subst (λ M → M —↠[ []ˢ ] blame)
        (sym focus-blame) ↠-refl)
source-path-blame {W = W} path focus-blame
  | changesL , source-steps , evolve =
    changesL , source-steps , evolve evolutions-refl
