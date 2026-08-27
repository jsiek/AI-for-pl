{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseContextDef where

-- File Charter:
--   * Defines the CTI-indexed evaluation-context zipper for proving forward
--     target-reveal/rebase closing without a separate world-frame stack.
--   * Keeps every nested world in the CTI node that owns it and records the
--     source reduct reconstructed by each store-changing evaluation frame.
--   * States the generalized induction and its adapter to the unchanged
--     SimTargetRevealRebaseClosing interface.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; TyVar; ★; ＇_; _⇒_; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using
  ( Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_; rename↑; rename↓ )
open import Imprecision using (VarImp; X⊑★; _⊑_; ⇒⊑⇒)
open import Primitives using (Prim; primArgTy; primResultTy)
open import CastTerms using
  ( Ctx; Δᵉ; Σᵉ; Term; Value; ⟨_,_,_⟩; _·_; _⦂∀_[_]
  ; _⟨_⟩; _↑_; _↓_; _⊕[_]_
  )
open import Reduction using
  ( StoreChange; StoreChanges; applyStore; applyTy; applyTys; applyTerm
  ; applyBody; applyConsistency; applyConsistencies; applyVar
  ; applyTerms; _—→[_]_; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.Reduction using
  (applyBodies; applyReveals; applyConceals)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  ( generator-absent; revealGeneratorPosition; concealGeneratorPosition )
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


------------------------------------------------------------------------
-- A CTI node with all of its indices existentially packaged
------------------------------------------------------------------------

data RelatedConfiguration (Δᴸ Δᴿ : TyCtx) : Set₁ where
  pack : ∀ {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ CTI.⊢² M ⊑ M′ ∶ p
    → RelatedConfiguration Δᴸ Δᴿ

sourceTerm : ∀ {Δᴸ Δᴿ}
  → RelatedConfiguration Δᴸ Δᴿ → Term Δᴸ
sourceTerm (pack {M = M} related) = M

targetTerm : ∀ {Δᴸ Δᴿ}
  → RelatedConfiguration Δᴸ Δᴿ → Term Δᴿ
targetTerm (pack {M′ = M′} related) = M′


------------------------------------------------------------------------
-- One store-changing evaluation-context descent through CTI
------------------------------------------------------------------------

infix 4 _↘ᶜ_

data _↘ᶜ_ {Δᴸ Δᴿ : TyCtx} :
    RelatedConfiguration Δᴸ Δᴿ →
    RelatedConfiguration Δᴸ Δᴿ → Set₁ where

  focus-·₁ : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    → pack (CTI.·⊑·² function-rel argument-rel) ↘ᶜ pack function-rel

  focus-·₂ : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    → Value L
    → pack (CTI.·⊑·² function-rel argument-rel) ↘ᶜ pack argument-rel

  focus-⊕₁ : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {op : Prim}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
      (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    → pack (CTI.⊕⊑⊕² op left-rel right-rel r) ↘ᶜ pack left-rel

  focus-⊕₂ : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {op : Prim}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
      (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    → Value L
    → pack (CTI.⊕⊑⊕² op left-rel right-rel r) ↘ᶜ pack right-rel

  focus-•-paired : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
      {A : Ty Δᴸ} {A′ : Ty Δᴿ}
      (p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ (`∀ C′))
      (related : γ CTI.⊢² M ⊑ M′ ∶ p∀)
      (q : A ⊑ᵀ⟨ γ ⟩ A′)
      (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
    → pack (CTI.•⊑•² p∀ related q r) ↘ᶜ pack related

  focus-•-source : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
      (p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ B)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p∀)
      (q : A ⊑ᵀ⟨ γ ⟩ ★)
      (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.•⊑² p∀ related q r) ↘ᶜ pack related

  focus-cast-paired : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {C A : Ty Δᴸ} {C′ A′ : Ty Δᴿ}
      {p : C ⊑ᵀ⟨ γ ⟩ C′}
      {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
      (c : ν ⊢ C ∼ A) (c′ : ν′ ⊢ C′ ∼ A′)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ A′)
    → pack (CTI.cast⊑cast² c c′ related q) ↘ᶜ pack related

  focus-cast-target : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {ν : Env∼ Δᴿ}
      (c′ : ν ⊢ B ∼ B′)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑cast² c′ related q) ↘ᶜ pack related

  focus-cast-source : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {ν : Env∼ Δᴸ}
      (c : ν ⊢ A ∼ A′)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.cast⊑² c related q) ↘ᶜ pack related


------------------------------------------------------------------------
-- Conversion frames.  The child world is read from the CTI child itself.
------------------------------------------------------------------------

  focus-target-reveal-identity : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ} {Xᴿ : TyVar Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
      (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
      (absent : revealGeneratorPosition c′⊢ ≡ generator-absent)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑reveal-identity c′⊢ absent related q) ↘ᶜ pack related

  focus-target-conceal-identity : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ} {Xᴿ : TyVar Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
      (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
      (absent : concealGeneratorPosition c′⊢ ≡ generator-absent)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑conceal-identity c′⊢ absent related q) ↘ᶜ pack related

  focus-source-reveal-identity : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv↑ Δᴸ A A′}
      (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
      (absent : revealGeneratorPosition c⊢ ≡ generator-absent)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.reveal⊑-identity c⊢ absent related q) ↘ᶜ pack related

  focus-source-conceal-identity : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv↓ Δᴸ A A′}
      (c⊢ : Σᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
      (absent : concealGeneratorPosition c⊢ ≡ generator-absent)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.conceal⊑-identity c⊢ absent related q) ↘ᶜ pack related

  focus-source-reveal-only : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv↑ Δᴸ A A′}
      (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
      (present : revealGeneratorPosition c⊢ ≢ generator-absent)
      (mark : marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★)
      (free : ∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ ≢
        toRenameⁱ (ηᴸᶜ γ) Xᴸ)
      (represented : Rᴸ ⊑ᵀ⟨ γ ⟩ ★)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.reveal⊑-only² c⊢ present mark free represented related q)
        ↘ᶜ pack related

  focus-source-conceal-only : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv↓ Δᴸ A A′}
      (c⊢ : Σᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
      (present : concealGeneratorPosition c⊢ ≢ generator-absent)
      (mark : marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★)
      (free : ∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ ≢
        toRenameⁱ (ηᴸᶜ γ) Xᴸ)
      (represented : Rᴸ ⊑ᵀ⟨ γ ⟩ ★)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.conceal⊑-only² c⊢ present mark free represented related q)
        ↘ᶜ pack related

  focus-reveal-paired : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A B Rᴸ : Ty Δᴸ} {A′ B′ Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
      (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
      (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
      (positions : revealGeneratorPosition c⊢ ≡
        revealGeneratorPosition c′⊢)
      (aligned : toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡
        toRenameⁱ (ηᴿᶜ γ) Xᴿ)
      (representation-rel : Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ)
      {p : A ⊑ᵀ⟨ γ ⟩ A′}
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : B ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned
        representation-rel related q) ↘ᶜ pack related

  focus-conceal-paired : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A B Rᴸ : Ty Δᴸ} {A′ B′ Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
      (c⊢ : Σᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
      (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
      (positions : concealGeneratorPosition c⊢ ≡
        concealGeneratorPosition c′⊢)
      (aligned : toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡
        toRenameⁱ (ηᴿᶜ γ) Xᴿ)
      (representation-rel : Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : B ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned
        representation-rel related q) ↘ᶜ pack related

  focus-target-reveal-rebase : ∀
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
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑reveal-rebase² c′⊢ rebase related q) ↘ᶜ pack related

  focus-target-conceal-rebase : ∀
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
      (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
      (rebase : SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ)
      (related : γᵖ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑conceal-rebase² c′⊢ rebase related q) ↘ᶜ pack related


------------------------------------------------------------------------
-- Reflexive-transitive evaluation-context zipper
------------------------------------------------------------------------

infix 4 _↘ᶜ*_

data _↘ᶜ*_ {Δᴸ Δᴿ : TyCtx} :
    RelatedConfiguration Δᴸ Δᴿ →
    RelatedConfiguration Δᴸ Δᴿ → Set₁ where
  focus-here : ∀ {related} → related ↘ᶜ* related
  focus-there : ∀ {outer middle focus}
    → outer ↘ᶜ middle
    → middle ↘ᶜ* focus
    → outer ↘ᶜ* focus

extend-focus : ∀ {Δᴸ Δᴿ}
    {outer middle focus : RelatedConfiguration Δᴸ Δᴿ}
  → outer ↘ᶜ* middle
  → middle ↘ᶜ focus
  → outer ↘ᶜ* focus
extend-focus focus-here edge = focus-there edge focus-here
extend-focus (focus-there outer-edge tail) edge =
  focus-there outer-edge (extend-focus tail edge)


------------------------------------------------------------------------
-- Source reduct reconstruction through the zipper
------------------------------------------------------------------------

rebuildSourceEdge : ∀ {Δᴸ Δᴿ Δᴸ′}
    {outer inner : RelatedConfiguration Δᴸ Δᴿ}
  → outer ↘ᶜ inner
  → StoreChange Δᴸ Δᴸ′
  → Term Δᴸ′
  → Term Δᴸ′
rebuildSourceEdge (focus-·₁ {M = M} function-rel argument-rel)
    χᴸ N = N · applyTerm χᴸ M
rebuildSourceEdge (focus-·₂ {L = L} function-rel argument-rel source-value)
    χᴸ N = applyTerm χᴸ L · N
rebuildSourceEdge (focus-⊕₁ {M = M} {op = op} left-rel right-rel r)
    χᴸ N = N ⊕[ op ] applyTerm χᴸ M
rebuildSourceEdge
    (focus-⊕₂ {L = L} {op = op} left-rel right-rel r source-value)
    χᴸ N = applyTerm χᴸ L ⊕[ op ] N
rebuildSourceEdge
    (focus-•-paired {C = C} {A = A} p∀ related q r)
    χᴸ N = N ⦂∀ applyBody χᴸ C [ applyTy χᴸ A ]
rebuildSourceEdge
    (focus-•-source {C = C} {A = A} p∀ related q r)
    χᴸ N = N ⦂∀ applyBody χᴸ C [ applyTy χᴸ A ]
rebuildSourceEdge (focus-cast-paired c c′ related q) χᴸ N =
  N ⟨ applyConsistency χᴸ c ⟩
rebuildSourceEdge (focus-cast-target c′ related q) χᴸ N = N
rebuildSourceEdge (focus-cast-source c related q) χᴸ N =
  N ⟨ applyConsistency χᴸ c ⟩
rebuildSourceEdge
    (focus-target-reveal-identity c′⊢ absent related q) χᴸ N = N
rebuildSourceEdge
    (focus-target-conceal-identity c′⊢ absent related q) χᴸ N = N
rebuildSourceEdge
    (focus-source-reveal-identity {c = c} c⊢ absent related q) χᴸ N =
  N ↑ rename↑ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-source-conceal-identity {c = c} c⊢ absent related q) χᴸ N =
  N ↓ rename↓ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-source-reveal-only {c = c} c⊢ present mark free represented
      related q) χᴸ N =
  N ↑ rename↑ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-source-conceal-only {c = c} c⊢ present mark free represented
      related q) χᴸ N =
  N ↓ rename↓ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-reveal-paired {c = c} c⊢ c′⊢ positions aligned
      representation-rel related q) χᴸ N =
  N ↑ rename↑ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-conceal-paired {c = c} c⊢ c′⊢ positions aligned
      representation-rel related q) χᴸ N =
  N ↓ rename↓ (λ X → applyVar χᴸ X) c
rebuildSourceEdge
    (focus-target-reveal-rebase c′⊢ rebase related q) χᴸ N = N
rebuildSourceEdge
    (focus-target-conceal-rebase c′⊢ rebase related q) χᴸ N = N

data RebuildSourceEdge {Δᴸ Δᴿ Δᴸ′}
    {outer inner : RelatedConfiguration Δᴸ Δᴿ}
    (edge : outer ↘ᶜ inner)
    (χᴸ : StoreChange Δᴸ Δᴸ′)
    (inner-result : Term Δᴸ′) : Term Δᴸ′ → Set where

  rebuild-edge : ∀ {outer-result}
    → outer-result ≡ rebuildSourceEdge edge χᴸ inner-result
    → RebuildSourceEdge edge χᴸ inner-result outer-result

data RebuildSource {Δᴸ Δᴿ Δᴸ′} :
    {outer focus : RelatedConfiguration Δᴸ Δᴿ}
    → (path : outer ↘ᶜ* focus)
    → (χᴸ : StoreChange Δᴸ Δᴸ′)
    → (focus-result : Term Δᴸ′)
    → Term Δᴸ′ → Set₁ where

  rebuild-here : ∀ {related : RelatedConfiguration Δᴸ Δᴿ}
      {χᴸ : StoreChange Δᴸ Δᴸ′} {focus-result result : Term Δᴸ′}
    → result ≡ focus-result
    → RebuildSource {outer = related} {focus = related}
        focus-here χᴸ focus-result result

  rebuild-there : ∀
      {outer focus middle : RelatedConfiguration Δᴸ Δᴿ}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {focus-result middle-result outer-result : Term Δᴸ′}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
    → RebuildSource tail χᴸ focus-result middle-result
    → RebuildSourceEdge edge χᴸ middle-result outer-result
    → RebuildSource (focus-there edge tail) χᴸ focus-result outer-result

extend-rebuild : ∀ {Δᴸ Δᴿ Δᴸ′}
    {outer middle focus : RelatedConfiguration Δᴸ Δᴿ}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {focus-result middle-result outer-result : Term Δᴸ′}
  → RebuildSource path χᴸ middle-result outer-result
  → RebuildSourceEdge edge χᴸ focus-result middle-result
  → RebuildSource (extend-focus path edge) χᴸ focus-result outer-result
extend-rebuild (rebuild-here refl) edge-rebuild =
  rebuild-there (rebuild-here refl) edge-rebuild
extend-rebuild (rebuild-there tail-rebuild outer-rebuild) edge-rebuild =
  rebuild-there (extend-rebuild tail-rebuild edge-rebuild) outer-rebuild


------------------------------------------------------------------------
-- Generalized induction and adapter to the unchanged public interface
------------------------------------------------------------------------

ContextualTargetRevealRebaseClosingᵀ : Set₁
ContextualTargetRevealRebaseClosingᵀ = ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → (root-related : γᵖ CTI.⊢² M ⊑ M′ ∶ p)
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → ∀ {Σᴸᶠ : TyStore Δᴸ} {Σᴿᶠ : TyStore Δᴿ}
      {Γᴸᶠ : TermCtx Δᴸ} {Γᴿᶠ : TermCtx Δᴿ}
      {γᶠ : ⟨ Δᴸ , Σᴸᶠ , Γᴸᶠ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿᶠ , Γᴿᶠ ⟩}
      {L : Term Δᴸ} {L′ : Term Δᴿ}
      {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
      (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (path : pack root-related ↘ᶜ* pack focus-related)
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
    Σ[ r ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↑ c′ —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² N ⊑ N′ ∶ r)

contextual-closing-adapter :
    ContextualTargetRevealRebaseClosingᵀ
  → SimTargetRevealRebaseClosingᵀ
contextual-closing-adapter close no-open c′⊢ rebase related q step =
  close no-open c′⊢ rebase related q related focus-here step
    (rebuild-here refl)
