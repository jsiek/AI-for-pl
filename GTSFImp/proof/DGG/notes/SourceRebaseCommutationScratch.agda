{-# OPTIONS --safe #-}

module SourceRebaseCommutationScratch where

-- File Charter:
--   * Probes source-bind/source-rebase commutation without changing the live
--     world, CTI, or transport interfaces.
--   * Checks the direct conceal square, protected-scope stack pop, and the
--     lift-left protected-pivot obstruction.
--   * Serves only as design evidence; it exports no production interface.

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; subst; sym; trans; cong)
open import Types using (Ty; TyVar; ＇_; renameᵗ)
open import Imprecision using (X⊑X)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import TyStore using (TyStore; lookupStore)
open import TermCtx using (TermCtx)
open import CastTerms using (⟨_,_,_⟩; Δᵉ)
open import proof.DGG.World using
  ( _⊑ᶜ_; _▻ᶜ_; _⊑ᵀ⟨_⟩_; bind-left-changeᶜ
  ; centerᶜ; ηᴸᶜ; ηᴿᶜ
  ; CanRebaseSourceᵗ; can-rebase-sourceᵗ
  ; InsertSourceᵗ; insert-hereᵗ; insert-skipᵗ
  ; rebaseSourceEmbeddingᵗ
  ; rebaseSource-alignedᵗ; rebaseSource-offᵗ
  ; rebase-source-changeᶜ
  ; bind-termᶜ; liftBothᶜ; liftLeftᶜ
  )
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now; source-rebase-bind-left)
open import proof.DGG.TransportSourceBindDef using
  ( SourceBindScope; source-scope-root; source-scope-term
  ; source-scope-both; source-scope-left; source-scope-center
  ; source-scope-left-commutes; source-scope-right-commutes
  )
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)


source-conceal-square : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
  → SourceBindScope ρ γ γ⁺
  → Σ[ γᵖ⁺ ∈ (⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩) ]
      (SourceBindScope ρ γᵖ γᵖ⁺ ×
       SourceRebaseᶜ γᵖ⁺ γ⁺ (toRenameᵗ ρ Xᴸ) Xᴿ)
source-conceal-square {γᵖ = γᵖ} {γ = γ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    rebase (source-scope-root {C = C} eqᴸ) =
  (γᵖ ▻ᶜ bind-left-changeᶜ C eqᴸ) , source-scope-root eqᴸ ,
    subst (λ Z → SourceRebaseᶜ
        (γᵖ ▻ᶜ bind-left-changeᶜ C eqᴸ)
        (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Z Xᴿ)
      (sym (toRename-wk-eq Xᴸ))
      (source-rebase-bind-left C rebase eqᴸ eqᴸ)


source-scope-rebase-left-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → (eq-X : toRenameᵗ ρ X ≡ X⁺)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γ) X (toRenameᵗ (ηᴿᶜ γ) Y))
  → (ok⁺ : CanRebaseSourceᵗ
      (ηᴸᶜ γ⁺) X⁺ (toRenameᵗ (ηᴿᶜ γ⁺) Y))
  → ∀ Z
  → toRenameᵗ (source-scope-center plan)
      (toRenameᵗ (rebaseSourceEmbeddingᵗ ok) Z)
    ≡ toRenameᵗ (rebaseSourceEmbeddingᵗ ok⁺)
        (toRenameᵗ ρ Z)
source-scope-rebase-left-commutes {ρ = ρ} {X = X} {Y = Y}
    plan eq-X ok ok⁺ Z with Z Fin.≟ X
source-scope-rebase-left-commutes {ρ = ρ} {Y = Y}
    plan eq-X ok ok⁺ Z | yes same =
  trans
    (cong (toRenameᵗ (source-scope-center plan))
      (trans
        (cong (toRenameᵗ (rebaseSourceEmbeddingᵗ ok)) same)
        (rebaseSource-alignedᵗ ok)))
    (trans (source-scope-right-commutes plan Y)
      (sym (trans
        (cong (toRenameᵗ (rebaseSourceEmbeddingᵗ ok⁺))
          (trans (cong (toRenameᵗ ρ) same) eq-X))
        (rebaseSource-alignedᵗ ok⁺))))
source-scope-rebase-left-commutes {ρ = ρ} {X = X} {Y = Y}
    plan eq-X ok ok⁺ Z | no Z≠X =
  trans
    (cong (toRenameᵗ (source-scope-center plan))
      (rebaseSource-offᵗ ok Z Z≠X))
    (trans (source-scope-left-commutes plan Z)
      (sym (rebaseSource-offᵗ ok⁺ (toRenameᵗ ρ Z) image-apart)))
  where
  image-apart : toRenameᵗ ρ Z ≢ _
  image-apart same = Z≠X
    (toRenameᵗ-injective ρ (trans same (sym eq-X)))


protected-pivot-can-rebase : CanRebaseSourceᵗ
    (keep (skip (keep (empty {Δ = Nat.zero}))))
    Fin.zero (Fin.suc Fin.zero)
protected-pivot-can-rebase =
  can-rebase-sourceᵗ (λ ()) (insert-skipᵗ insert-hereᵗ)


protected-pivot-cannot-commute : CanRebaseSourceᵗ
    (keep (keep (skip (keep (empty {Δ = Nat.zero}))))) Fin.zero
    (Fin.suc (Fin.suc Fin.zero))
  → ⊥
protected-pivot-cannot-commute
    (can-rebase-sourceᵗ apart (insert-skipᵗ ()))


data DirectSourceScopeSquare : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ}
  → (ρ : Δᴸ ↪ᵗ Δᴸ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → TyVar Δᴸ → TyVar Δᴸ⁺ → TyVar Δᴿ → Set where

  direct-source-scope-square : ∀
      {Δᴸ Δᴸ⁺ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ}
      {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
    → (plan : SourceBindScope ρ γ γ⁺)
    → (eq-X : toRenameᵗ ρ X ≡ X⁺)
    → (ok : CanRebaseSourceᵗ
        (ηᴸᶜ γ) X (toRenameᵗ (ηᴿᶜ γ) Y))
    → (represented : (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Y)
    → (ok⁺ : CanRebaseSourceᵗ
        (ηᴸᶜ γ⁺) X⁺ (toRenameᵗ (ηᴿᶜ γ⁺) Y))
    → (represented⁺ : (＇ X⁺) ⊑ᵀ⟨ γ⁺ ⟩ lookupStore Σᴿ Y)
    → DirectSourceScopeSquare ρ γ γ⁺
        (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented)
        (γ⁺ ▻ᶜ rebase-source-changeᶜ X⁺ Y ok⁺ represented⁺)
        X X⁺ Y


pop-direct-source-scope-square : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ}
    {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
  → SourceRebaseᶜ γ γᵖ X Y
  → DirectSourceScopeSquare ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
  → SourceBindScope ρ γ γ⁺ × SourceRebaseᶜ γ⁺ γᵖ⁺ X⁺ Y
pop-direct-source-scope-square
    (source-rebase-now ok represented)
    (direct-source-scope-square plan eq-X ok represented ok⁺ represented⁺) =
  plan , source-rebase-now ok⁺ represented⁺


data ScopedSourceRebaseᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → Γᴸ ⊑ᶜ Γᴿ
    → TyVar (Δᵉ Γᴸ) → TyVar (Δᵉ Γᴿ) → Set where

  scoped-rebase-direct : ∀ {Γᴸ Γᴿ}
      {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {X Y}
    → SourceRebaseᶜ γ γᵖ X Y
    → ScopedSourceRebaseᶜ γ γᵖ X Y

  scoped-rebase-term : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → ScopedSourceRebaseᶜ γ γᵖ X Y
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (pᵖ : A ⊑ᵀ⟨ γᵖ ⟩ B)
    → ScopedSourceRebaseᶜ
        (bind-termᶜ γ p) (bind-termᶜ γᵖ pᵖ) X Y

  scoped-rebase-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → ScopedSourceRebaseᶜ γ γᵖ X Y
    → ScopedSourceRebaseᶜ
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γᵖ)
        (Fin.suc X) (Fin.suc Y)

  scoped-rebase-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → ScopedSourceRebaseᶜ γ γᵖ X Y
    → ScopedSourceRebaseᶜ
        (liftLeftᶜ γ) (liftLeftᶜ γᵖ) (Fin.suc X) Y


data SourceScopeRebaseStack : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ}
  → (ρ : Δᴸ ↪ᵗ Δᴸ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → TyVar Δᴸ → TyVar Δᴸ⁺ → TyVar Δᴿ → Set where

  stack-direct : ∀
      {Δᴸ Δᴸ⁺ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ}
      {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
    → DirectSourceScopeSquare ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
    → SourceScopeRebaseStack ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y

  stack-term : ∀
      {Δᴸ Δᴸ⁺ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ}
      {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → SourceScopeRebaseStack ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : renameᵗ (toRenameᵗ ρ) A ⊑ᵀ⟨ γ⁺ ⟩ B)
    → (pᵖ : A ⊑ᵀ⟨ γᵖ ⟩ B)
    → (pᵖ⁺ : renameᵗ (toRenameᵗ ρ) A ⊑ᵀ⟨ γᵖ⁺ ⟩ B)
    → SourceScopeRebaseStack ρ
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)
        (bind-termᶜ γᵖ pᵖ) (bind-termᶜ γᵖ⁺ pᵖ⁺) X X⁺ Y

  stack-both : ∀
      {Δᴸ Δᴸ⁺ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ}
      {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
    → SourceScopeRebaseStack ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
    → SourceScopeRebaseStack (keep ρ)
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γ⁺)
        (liftBothᶜ X⊑X γᵖ) (liftBothᶜ X⊑X γᵖ⁺)
        (Fin.suc X) (Fin.suc X⁺) (Fin.suc Y)

  stack-left : ∀
      {Δᴸ Δᴸ⁺ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ}
      {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
    → SourceScopeRebaseStack ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
    → SourceScopeRebaseStack (keep ρ)
        (liftLeftᶜ γ) (liftLeftᶜ γ⁺)
        (liftLeftᶜ γᵖ) (liftLeftᶜ γᵖ⁺)
        (Fin.suc X) (Fin.suc X⁺) Y


pop-source-scope-stack : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ}
    {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar Δᴸ} {X⁺ : TyVar Δᴸ⁺} {Y : TyVar Δᴿ}
  → ScopedSourceRebaseᶜ γ γᵖ X Y
  → SourceScopeRebaseStack ρ γ γ⁺ γᵖ γᵖ⁺ X X⁺ Y
  → SourceBindScope ρ γ γ⁺ × ScopedSourceRebaseᶜ γ⁺ γᵖ⁺ X⁺ Y
pop-source-scope-stack (scoped-rebase-direct rebase)
    (stack-direct square)
    with pop-direct-source-scope-square rebase square
pop-source-scope-stack (scoped-rebase-direct rebase)
    (stack-direct square) | plan , rebase⁺ =
  plan , scoped-rebase-direct rebase⁺

pop-source-scope-stack
    (scoped-rebase-term rebase p pᵖ)
    (stack-term stack p p⁺ pᵖ pᵖ⁺)
    with pop-source-scope-stack rebase stack
pop-source-scope-stack
    (scoped-rebase-term rebase p pᵖ)
    (stack-term stack p p⁺ pᵖ pᵖ⁺) | plan , rebase⁺ =
  source-scope-term plan p p⁺ ,
    scoped-rebase-term rebase⁺ p⁺ pᵖ⁺

pop-source-scope-stack (scoped-rebase-both rebase)
    (stack-both stack) with pop-source-scope-stack rebase stack
pop-source-scope-stack (scoped-rebase-both rebase)
    (stack-both stack) | plan , rebase⁺ =
  source-scope-both plan , scoped-rebase-both rebase⁺

pop-source-scope-stack (scoped-rebase-left rebase)
    (stack-left stack) with pop-source-scope-stack rebase stack
pop-source-scope-stack (scoped-rebase-left rebase)
    (stack-left stack) | plan , rebase⁺ =
  source-scope-left plan , scoped-rebase-left rebase⁺
