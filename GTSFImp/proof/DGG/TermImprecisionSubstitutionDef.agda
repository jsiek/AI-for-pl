{-# OPTIONS --safe #-}

module proof.DGG.TermImprecisionSubstitutionDef where

-- File Charter:
--   * States single-variable substitution for canonical cast-term
--     imprecision.
--   * Defines the typed parallel substitution scope needed to recurse below
--     term and type binders without exchanging world-history constructors.
--   * Relates the two substituted bodies using the relation between the two
--     substituted values and the term-bound world of the body derivation.
--   * Contains no substitution proof.

open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyVar)
open import Imprecision using (X⊑X)
open import TyStore using (TyStore)
import TermCtx as TC
open import TermCtx using (TermCtx)
open import CastTerms using
  ( Ctx
  ; Δᵉ
  ; Term
  ; Subst
  ; _[_]
  ; ⟨_,_,_⟩
  ; _⊢_⦂_
  ; subst
  ; exts
  ; liftˢ
  )
open import proof.TermInTermSubst using (SubstWf)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)


record TermSubstScope
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
    (γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩)
    (σᴸ : Subst Δᴸ) (σᴿ : Subst Δᴿ) : Set where
  field
    scope-⊑ᵀ : ∀ {A B}
      → A ⊑ᵀ⟨ γ ⟩ B
      → A ⊑ᵀ⟨ γˢ ⟩ B

    scope-source-wf : SubstWf Δᴸ Σᴸ Γᴸ Ψᴸ σᴸ
    scope-target-wf : SubstWf Δᴿ Σᴿ Γᴿ Ψᴿ σᴿ

    scope-variable : ∀ {x A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
      → Γᴸ TC.∋ x ⦂ A
      → Γᴿ TC.∋ x ⦂ B
      → γˢ ⊢² σᴸ x ⊑ σᴿ x ∶ scope-⊑ᵀ p

    scope-source-mark : ∀ {X v}
      → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ v
      → marksᶜ γˢ (toRenameⁱ (ηᴸᶜ γˢ) X) ≡ v

    scope-source-unoccupied : ∀ {X}
      → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y
          ≢ toRenameⁱ (ηᴸᶜ γ) X)
      → (∀ Y → toRenameⁱ (ηᴿᶜ γˢ) Y
          ≢ toRenameⁱ (ηᴸᶜ γˢ) X)

    scope-aligned : ∀ {X Y}
      → toRenameⁱ (ηᴸᶜ γ) X ≡ toRenameⁱ (ηᴿᶜ γ) Y
      → toRenameⁱ (ηᴸᶜ γˢ) X ≡ toRenameⁱ (ηᴿᶜ γˢ) Y

open TermSubstScope public


ExtendTermSubstScopeᵀ : Set
ExtendTermSubstScopeᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (scope : TermSubstScope γ γˢ σᴸ σᴿ)
  → TermSubstScope (bind-termᶜ γ p)
      (bind-termᶜ γˢ (scope-⊑ᵀ scope p)) (exts σᴸ) (exts σᴿ)


LiftBothTermSubstScopeᵀ : Set
LiftBothTermSubstScopeᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
  → TermSubstScope γ γˢ σᴸ σᴿ
  → TermSubstScope (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γˢ)
      (liftˢ σᴸ) (liftˢ σᴿ)


LiftLeftTermSubstScopeᵀ : Set
LiftLeftTermSubstScopeᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
  → TermSubstScope γ γˢ σᴸ σᴿ
  → TermSubstScope (liftLeftᶜ γ) (liftLeftᶜ γˢ)
      (liftˢ σᴸ) σᴿ


PushTermSubstRebaseᵀ : Set
PushTermSubstRebaseᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ} {X Y}
  → (scope : TermSubstScope γ γˢ σᴸ σᴿ)
  → SourceRebaseᶜ γ γᵖ X Y
  → Σ[ γᵖˢ ∈ (⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩) ]
      TermSubstScope γᵖ γᵖˢ σᴸ σᴿ
      × SourceRebaseᶜ γˢ γᵖˢ X Y


PopTermSubstRebaseᵀ : Set
PopTermSubstRebaseᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ} {X Y}
  → (scope : TermSubstScope γ γˢ σᴸ σᴿ)
  → SourceRebaseᶜ γᵖ γ X Y
  → Σ[ γᵖˢ ∈ (⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩) ]
      TermSubstScope γᵖ γᵖˢ σᴸ σᴿ
      × SourceRebaseᶜ γᵖˢ γˢ X Y


TermImprecisionParallelSubstitutionᵀ : Set
TermImprecisionParallelSubstitutionᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ Ψᴸ : TermCtx Δᴸ} {Γᴿ Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γˢ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (scope : TermSubstScope γ γˢ σᴸ σᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → γˢ ⊢² subst σᴸ M ⊑ subst σᴿ M′ ∶ scope-⊑ᵀ scope p


TermImprecisionSubstitutionᵀ : Set
TermImprecisionSubstitutionᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {N : Term (Δᵉ Γᴸ)} {N′ : Term (Δᵉ Γᴿ)}
    {A B : Ty (Δᵉ Γᴸ)} {A′ B′ : Ty (Δᵉ Γᴿ)}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → γ ⊢² V ⊑ V′ ∶ pA
  → bind-termᶜ γ pA ⊢² N ⊑ N′ ∶ pB
  → γ ⊢² N [ V ] ⊑ N′ [ V′ ] ∶ pB
