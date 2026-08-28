{-# OPTIONS --safe #-}

module proof.DGG.notes.ContextualSimPromotionProbe where

-- File Charter:
--   * Probes a whole-root contextual form of forward simulation over the live
--     full-context CTI zipper.
--   * Requires target readiness before a right-focused descent and returns
--     the ordinary public Sim conclusion for the rebuilt whole source term.
--   * Pins application-left and the trusted aligned allocation that changes
--     two nested target-rebase frames into a paired outer reveal with one
--     surviving inner target-rebase frame.
--
-- The worker deliberately does not accept a focus-local simulation result and
-- then replay the old path.  Such replay is unsound for an aligned bind: a
-- sibling CTI may depend on the discharged frame, and the trusted allocation
-- below changes the path shape.  The whole-root result is instead the semantic
-- context boundary.  A proof must synchronize siblings while descending,
-- using contextual catchup and the context-aware value boundaries.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; ⟨_,_,_⟩; _·_)
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys; applyTerm
  ; bind; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)

import Imprecision as I
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.Examples.TargetIdentityReveal as TIR
import proof.DGG.OneStep as Step
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SourceRebase using (source-rebase-now)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-bind-left-aligned)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; evolutions-refl; evolutions-step-left )


------------------------------------------------------------------------
-- Exact proposed whole-root contextual simulation statement
------------------------------------------------------------------------

ContextualSimᵀ : Set₁
ContextualSimᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (root-related : γ CTI.⊢² M ⊑ M′ ∶ p)
  → ∀ {γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {L : Term Δᴸ} {L′ : Term Δᴿ}
      {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
      (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (path : pack root-related ↘ᶜ* pack focus-related)
  → TargetReady path
  → ∀ {P : Term Δᴸ′}
  → L —→[ χᴸ ] P
  → RebuildSource path χᴸ P N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² N ⊑ N′ ∶ q)

contextual-sim-adapter : ContextualSimᵀ → Simᵀ
contextual-sim-adapter sim no-open related step =
  sim no-open related related focus-here tt step (rebuild-here refl)


------------------------------------------------------------------------
-- Ordinary application-left is a direct constructor-form instance
------------------------------------------------------------------------

contextual-sim-app-left :
    ContextualSimᵀ
  → ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {P : Term Δᴸ′}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → openFramesᶜ γ ≡ []
  → (function-rel : γ CTI.⊢² L ⊑ L′ ∶ I.⇒⊑⇒ pA pB)
  → (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
  → L —→[ χᴸ ] P
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ applyTy χᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      ((L′ · M′) —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² (P · applyTerm χᴸ M) ⊑ N′ ∶ q)
contextual-sim-app-left sim no-open function-rel argument-rel step =
  sim no-open (CTI.·⊑·² function-rel argument-rel) function-rel
    (focus-there (focus-·₁ function-rel argument-rel) focus-here)
    tt step
    (rebuild-there (rebuild-here refl) (rebuild-edge refl))


------------------------------------------------------------------------
-- Trusted aligned allocation: the old path is not replayable
------------------------------------------------------------------------

tir-before-allocation-path :
  pack TIR.checkpoint₁-reveals-imprecision ↘ᶜ*
    pack TIR.checkpoint₁-function-imprecision
tir-before-allocation-path =
  focus-there
    (focus-target-reveal-rebase
      TIR.checkpoint₁-alpha-reveal⊢
      (source-rebase-now TIR.checkpoint₁-alpha-ok
        TIR.checkpoint₁-alpha-representation)
      (CTI.⊑reveal-rebase²
        TIR.checkpoint₁-beta-reveal⊢
        (source-rebase-now TIR.checkpoint₁-beta-ok
          TIR.checkpoint₁-beta-representation)
        TIR.checkpoint₁-function-imprecision
        (I.⇒⊑⇒ I.X⊑X I.★⊑★))
      (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★))
    (focus-there
      (focus-target-reveal-rebase
        TIR.checkpoint₁-beta-reveal⊢
        (source-rebase-now TIR.checkpoint₁-beta-ok
          TIR.checkpoint₁-beta-representation)
        TIR.checkpoint₁-function-imprecision
        (I.⇒⊑⇒ I.X⊑X I.★⊑★))
      focus-here)

tir-after-allocation-path :
  pack TIR.checkpoint₃-reveals-imprecision ↘ᶜ*
    pack TIR.checkpoint₃-function-imprecision
tir-after-allocation-path =
  focus-there
    (focus-reveal-paired
      TIR.checkpoint₃-source-reveal⊢
      TIR.checkpoint₁-alpha-reveal⊢
      refl refl I.ι⊑★
      TIR.checkpoint₃-beta-imprecision
      TIR.ℕ⇒★⊑★⇒★)
    (focus-there
      (focus-target-reveal-rebase
        TIR.checkpoint₁-beta-reveal⊢
        (source-rebase-now TIR.checkpoint₃-beta-ok
          TIR.checkpoint₃-beta-representation)
        TIR.checkpoint₃-function-imprecision
        (I.⇒⊑⇒ I.X⊑X I.★⊑★))
      focus-here)

tir-before-allocation-ready : TargetReady tir-before-allocation-path
tir-before-allocation-ready = tt

tir-after-allocation-ready : TargetReady tir-after-allocation-path
tir-after-allocation-ready = tt

tir-aligned-beta-inst-step :
  TIR.more-checkpoint₂ —→[ bind TIR.ℕᵗ ] TIR.more-checkpoint₃
tir-aligned-beta-inst-step = Step.reduction TIR.more-step₂

tir-root-aligned-evolution :
  MultiWorldEvolution
    {W = TIR.checkpoint₁-world} {W′ = TIR.checkpoint₃-world}
    (bind TIR.ℕᵗ ∷ˢ []ˢ) []ˢ
tir-root-aligned-evolution =
  evolutions-step-left refl
    (evolution-bind-left-aligned refl
      TIR.checkpoint₃-alpha-ok
      TIR.checkpoint₃-alpha-boundary
      TIR.checkpoint₃-alpha-representation)
    evolutions-refl

tir-final-cti-shape :
  TIR.checkpoint₃-reveals-imprecision ≡
    CTI.reveal⊑reveal²
      TIR.checkpoint₃-source-reveal⊢
      TIR.checkpoint₁-alpha-reveal⊢
      refl refl I.ι⊑★
      (CTI.⊑reveal-rebase²
        TIR.checkpoint₁-beta-reveal⊢
        (source-rebase-now TIR.checkpoint₃-beta-ok
          TIR.checkpoint₃-beta-representation)
        TIR.checkpoint₃-function-imprecision
        (I.⇒⊑⇒ I.X⊑X I.★⊑★))
      TIR.ℕ⇒★⊑★⇒★
tir-final-cti-shape = refl
