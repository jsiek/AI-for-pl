{-# OPTIONS --safe #-}

module proof.DGG.notes.ContextualSimClosingBoundaryProbe where

-- File Charter:
--   * Records the exact boundary mismatch found while starting the
--     ContextualSim proof skeleton.
--   * Defines a constructor-form witness that identifies one selected target
--     reveal/source-rebase edge inside an arbitrary caller zipper.
--   * States the smallest whole-caller widening of contextual reveal/rebase
--     closing and checks that it specializes to the existing boundary.
--
-- The existing ContextualTargetRevealRebaseClosingᵀ starts at the selected
-- reveal: its root target is the selected child wrapped by that reveal.  A
-- ContextualSim caller may have application, primitive, cast, or conversion
-- frames above the selected reveal.  Passing only the old inner path therefore
-- loses the caller target and source reconstruction.  The witness below keeps
-- one path, identifies the selected edge inside it, and permits path shape to
-- change in the final CTI rather than demanding unsound replay.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
open import CastTerms using (Term; Ctx; Δᵉ; ⟨_,_,_⟩)
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys
  ; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)

import Imprecision as I
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.Examples.TargetIdentityReveal as TIR
import proof.DGG.notes.ContextualSimPromotionProbe as CSP
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


------------------------------------------------------------------------
-- The selected reveal/rebase is an actual edge of the caller path
------------------------------------------------------------------------

data TargetRevealRebaseInPath
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
    (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    (related : γᵖ CTI.⊢² M ⊑ M′ ∶ p)
    (q : A ⊑ᵀ⟨ γ ⟩ B′) :
    {outer focus : RelatedConfiguration
      (⟨ Δᴸ , Σᴸ , Γᴸ ⟩) (⟨ Δᴿ , Σᴿ , Γᴿ ⟩)}
  → (path : outer ↘ᶜ* focus) → Set₁ where

  selected-here : ∀ {focus}
      {tail : pack related ↘ᶜ* focus}
    → TargetRevealRebaseInPath c′⊢ rebase related q
        (focus-there
          (focus-target-reveal-rebase c′⊢ rebase related q) tail)

  selected-there : ∀ {outer middle focus}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
    → TargetRevealRebaseInPath c′⊢ rebase related q tail
    → TargetRevealRebaseInPath c′⊢ rebase related q
        (focus-there edge tail)


------------------------------------------------------------------------
-- Exact smallest widening: the conclusion belongs to the caller root
------------------------------------------------------------------------

WholeContextualTargetRevealRebaseClosingᵀ : Set₁
WholeContextualTargetRevealRebaseClosingᵀ = ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {root-source : Term Δᴸ} {root-target : Term Δᴿ}
    {root-result : Term Δᴸ′}
    {root-source-type : Ty Δᴸ} {root-target-type : Ty Δᴿ}
    {root-type-related : root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
  → openFramesᶜ γ ≡ []
  → (root-related : γ CTI.⊢² root-source ⊑ root-target ∶
      root-type-related)
  → ∀ {inner-source : Term Δᴸ} {inner-target : Term Δᴿ}
      {inner-source-type : Ty Δᴸ}
      {inner-target-type selected-target-type Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {target-reveal : Conv↑ Δᴿ inner-target-type selected-target-type}
  → (target-reveal⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] target-reveal)
  → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
  → {inner-type-related :
      inner-source-type ⊑ᵀ⟨ γᵖ ⟩ inner-target-type}
  → (inner-related :
      γᵖ CTI.⊢² inner-source ⊑ inner-target ∶ inner-type-related)
  → (selected-type-related :
      inner-source-type ⊑ᵀ⟨ γ ⟩ selected-target-type)
  → ∀ {γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {L : Term Δᴸ} {L′ : Term Δᴿ}
      {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
      (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (path : pack root-related ↘ᶜ* pack focus-related)
  → TargetRevealRebaseInPath target-reveal⊢ rebase inner-related
      selected-type-related path
  → ∀ {P : Term Δᴸ′}
  → L —→[ χᴸ ] P
  → RebuildSource path χᴸ P root-result
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ final-related ∈
      applyTy χᴸ root-source-type ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ root-target-type ]
      (root-target —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ N′ ∶ final-related)


------------------------------------------------------------------------
-- The widened boundary strictly subsumes the existing below-reveal one
------------------------------------------------------------------------

whole-closing-specializes-to-current :
    WholeContextualTargetRevealRebaseClosingᵀ
  → ContextualTargetRevealRebaseClosingᵀ
whole-closing-specializes-to-current close no-open target-reveal⊢
    rebase inner-related selected-related focus-related tail step rebuild =
  close no-open
    (CTI.⊑reveal-rebase² target-reveal⊢ rebase inner-related
      selected-related)
    target-reveal⊢ rebase inner-related selected-related focus-related
    (focus-there
      (focus-target-reveal-rebase target-reveal⊢ rebase inner-related
        selected-related)
      tail)
    selected-here step
    (rebuild-there rebuild (rebuild-edge refl))


------------------------------------------------------------------------
-- Trusted non-top selection after aligned allocation
------------------------------------------------------------------------

tir-selected-inner-rebase :
  TargetRevealRebaseInPath
    TIR.checkpoint₁-beta-reveal⊢
    (source-rebase-now TIR.checkpoint₃-beta-ok
      TIR.checkpoint₃-beta-representation)
    TIR.checkpoint₃-function-imprecision
    (I.⇒⊑⇒ I.X⊑X I.★⊑★)
    CSP.tir-after-allocation-path
tir-selected-inner-rebase = selected-there selected-here
