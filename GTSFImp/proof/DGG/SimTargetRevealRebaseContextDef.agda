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
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

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

data RelatedConfiguration (Cᴸ Cᴿ : Ctx) : Set₁ where
  pack : ∀ {γ : Cᴸ ⊑ᶜ Cᴿ}
      {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ Cᴿ)}
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)} {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ CTI.⊢² M ⊑ M′ ∶ p
    → RelatedConfiguration Cᴸ Cᴿ

sourceTerm : ∀ {Cᴸ Cᴿ}
  → RelatedConfiguration Cᴸ Cᴿ → Term (Δᵉ Cᴸ)
sourceTerm (pack {M = M} related) = M

targetTerm : ∀ {Cᴸ Cᴿ}
  → RelatedConfiguration Cᴸ Cᴿ → Term (Δᵉ Cᴿ)
targetTerm (pack {M′ = M′} related) = M′


------------------------------------------------------------------------
-- One store-changing evaluation-context descent through CTI
------------------------------------------------------------------------

infix 4 _↘ᶜ_

data _↘ᶜ_ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ} :
    RelatedConfiguration (⟨ Δᴸ , Σᴸ , Γᴸ ⟩)
      (⟨ Δᴿ , Σᴿ , Γᴿ ⟩) →
    RelatedConfiguration (⟨ Δᴸ , Σᴸ , Γᴸ ⟩)
      (⟨ Δᴿ , Σᴿ , Γᴿ ⟩) → Set₁ where

  focus-·₁ : ∀
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    → pack (CTI.·⊑·² function-rel argument-rel) ↘ᶜ pack function-rel

  focus-·₂ : ∀
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    → Value L
    → pack (CTI.·⊑·² function-rel argument-rel) ↘ᶜ pack argument-rel

  focus-⊕₁ : ∀
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {op : Prim}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
      (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    → pack (CTI.⊕⊑⊕² op left-rel right-rel r) ↘ᶜ pack left-rel

  focus-⊕₂ : ∀
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {op : Prim}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
      (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    → Value L
    → pack (CTI.⊕⊑⊕² op left-rel right-rel r) ↘ᶜ pack right-rel

  focus-•-paired : ∀
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
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
      (p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ B)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p∀)
      (q : A ⊑ᵀ⟨ γ ⟩ ★)
      (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ B)
    → pack (CTI.•⊑² p∀ related q r) ↘ᶜ pack related

  focus-cast-paired : ∀
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
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {ν : Env∼ Δᴿ}
      (c′ : ν ⊢ B ∼ B′)
      (related : γ CTI.⊢² M ⊑ M′ ∶ p)
      (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → pack (CTI.⊑cast² c′ related q) ↘ᶜ pack related

  focus-cast-source : ∀
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

data _↘ᶜ*_ {Cᴸ Cᴿ : Ctx} :
    RelatedConfiguration Cᴸ Cᴿ →
    RelatedConfiguration Cᴸ Cᴿ → Set₁ where
  focus-here : ∀ {related} → related ↘ᶜ* related
  focus-there : ∀ {outer middle focus}
    → outer ↘ᶜ middle
    → middle ↘ᶜ* focus
    → outer ↘ᶜ* focus

extend-focus : ∀ {Cᴸ Cᴿ}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ* middle
  → middle ↘ᶜ focus
  → outer ↘ᶜ* focus
extend-focus focus-here edge = focus-there edge focus-here
extend-focus (focus-there outer-edge tail) edge =
  focus-there outer-edge (extend-focus tail edge)


------------------------------------------------------------------------
-- First-order source shapes and synchronized target path evolution
------------------------------------------------------------------------

data SourceFrame (Δ : TyCtx) : Set where
  app-leftᶠ : Term Δ → SourceFrame Δ
  app-rightᶠ : Term Δ → SourceFrame Δ
  primitive-leftᶠ : Prim → Term Δ → SourceFrame Δ
  primitive-rightᶠ : Prim → Term Δ → SourceFrame Δ
  paired-type-applicationᶠ :
    Ty (Nat.suc Δ) → Ty Δ → SourceFrame Δ
  source-type-applicationᶠ :
    Ty (Nat.suc Δ) → Ty Δ → SourceFrame Δ
  paired-castᶠ : ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → SourceFrame Δ
  target-castᶠ : SourceFrame Δ
  source-castᶠ : ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → SourceFrame Δ
  target-reveal-identityᶠ : SourceFrame Δ
  target-conceal-identityᶠ : SourceFrame Δ
  source-reveal-identityᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → SourceFrame Δ
  source-conceal-identityᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → SourceFrame Δ
  source-reveal-onlyᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → SourceFrame Δ
  source-conceal-onlyᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → SourceFrame Δ
  paired-revealᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → SourceFrame Δ
  paired-concealᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → SourceFrame Δ
  target-reveal-rebaseᶠ : SourceFrame Δ
  target-conceal-rebaseᶠ : SourceFrame Δ

rebuildFrame : ∀ {Δ Δ′}
  → SourceFrame Δ → StoreChange Δ Δ′ → Term Δ′ → Term Δ′
rebuildFrame (app-leftᶠ M) χ P = P · applyTerm χ M
rebuildFrame (app-rightᶠ L) χ P = applyTerm χ L · P
rebuildFrame (primitive-leftᶠ op M) χ P =
  P ⊕[ op ] applyTerm χ M
rebuildFrame (primitive-rightᶠ op L) χ P =
  applyTerm χ L ⊕[ op ] P
rebuildFrame (paired-type-applicationᶠ C A) χ P =
  P ⦂∀ applyBody χ C [ applyTy χ A ]
rebuildFrame (source-type-applicationᶠ C A) χ P =
  P ⦂∀ applyBody χ C [ applyTy χ A ]
rebuildFrame (paired-castᶠ c) χ P = P ⟨ applyConsistency χ c ⟩
rebuildFrame target-castᶠ χ P = P
rebuildFrame (source-castᶠ c) χ P = P ⟨ applyConsistency χ c ⟩
rebuildFrame target-reveal-identityᶠ χ P = P
rebuildFrame target-conceal-identityᶠ χ P = P
rebuildFrame (source-reveal-identityᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildFrame (source-conceal-identityᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c
rebuildFrame (source-reveal-onlyᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildFrame (source-conceal-onlyᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c
rebuildFrame (paired-revealᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildFrame (paired-concealᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c
rebuildFrame target-reveal-rebaseᶠ χ P = P
rebuildFrame target-conceal-rebaseᶠ χ P = P

sourceFrame : ∀ {Cᴸ Cᴿ}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner → SourceFrame (Δᵉ Cᴸ)
sourceFrame (focus-·₁ {M = M} function-rel argument-rel) = app-leftᶠ M
sourceFrame
    (focus-·₂ {L = L} function-rel argument-rel source-value) =
  app-rightᶠ L
sourceFrame (focus-⊕₁ {M = M} {op = op} left-rel right-rel r) =
  primitive-leftᶠ op M
sourceFrame
    (focus-⊕₂ {L = L} {op = op} left-rel right-rel r source-value) =
  primitive-rightᶠ op L
sourceFrame (focus-•-paired {C = C} {A = A} p∀ related q r) =
  paired-type-applicationᶠ C A
sourceFrame (focus-•-source {C = C} {A = A} p∀ related q r) =
  source-type-applicationᶠ C A
sourceFrame (focus-cast-paired c c′ related q) = paired-castᶠ c
sourceFrame (focus-cast-target c′ related q) = target-castᶠ
sourceFrame (focus-cast-source c related q) = source-castᶠ c
sourceFrame (focus-target-reveal-identity c′⊢ absent related q) =
  target-reveal-identityᶠ
sourceFrame (focus-target-conceal-identity c′⊢ absent related q) =
  target-conceal-identityᶠ
sourceFrame (focus-source-reveal-identity {c = c} c⊢ absent related q) =
  source-reveal-identityᶠ c
sourceFrame (focus-source-conceal-identity {c = c} c⊢ absent related q) =
  source-conceal-identityᶠ c
sourceFrame
    (focus-source-reveal-only {c = c}
      c⊢ present mark free represented related q) =
  source-reveal-onlyᶠ c
sourceFrame
    (focus-source-conceal-only {c = c}
      c⊢ present mark free represented related q) =
  source-conceal-onlyᶠ c
sourceFrame
    (focus-reveal-paired {c = c}
      c⊢ c′⊢ positions aligned represented related q) =
  paired-revealᶠ c
sourceFrame
    (focus-conceal-paired {c = c}
      c⊢ c′⊢ positions aligned represented related q) =
  paired-concealᶠ c
sourceFrame (focus-target-reveal-rebase c′⊢ rebase related q) =
  target-reveal-rebaseᶠ
sourceFrame (focus-target-conceal-rebase c′⊢ rebase related q) =
  target-conceal-rebaseᶠ

TargetEdgeReady : ∀ {Cᴸ Cᴿ}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner → Set
TargetEdgeReady (focus-·₁ function-rel argument-rel) = ⊤
TargetEdgeReady
    (focus-·₂ {L′ = L′} function-rel argument-rel source-value) =
  Value L′
TargetEdgeReady (focus-⊕₁ left-rel right-rel r) = ⊤
TargetEdgeReady
    (focus-⊕₂ {L′ = L′} left-rel right-rel r source-value) =
  Value L′
TargetEdgeReady (focus-•-paired p∀ related q r) = ⊤
TargetEdgeReady (focus-•-source p∀ related q r) = ⊤
TargetEdgeReady (focus-cast-paired c c′ related q) = ⊤
TargetEdgeReady (focus-cast-target c′ related q) = ⊤
TargetEdgeReady (focus-cast-source c related q) = ⊤
TargetEdgeReady (focus-target-reveal-identity c′⊢ absent related q) = ⊤
TargetEdgeReady (focus-target-conceal-identity c′⊢ absent related q) = ⊤
TargetEdgeReady (focus-source-reveal-identity c⊢ absent related q) = ⊤
TargetEdgeReady (focus-source-conceal-identity c⊢ absent related q) = ⊤
TargetEdgeReady
    (focus-source-reveal-only c⊢ present mark free represented related q) =
  ⊤
TargetEdgeReady
    (focus-source-conceal-only c⊢ present mark free represented related q) =
  ⊤
TargetEdgeReady
    (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q) =
  ⊤
TargetEdgeReady
    (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q) =
  ⊤
TargetEdgeReady (focus-target-reveal-rebase c′⊢ rebase related q) = ⊤
TargetEdgeReady (focus-target-conceal-rebase c′⊢ rebase related q) = ⊤

record TargetEdgeEvolution {Cᴸ Cᴿ Cᴿ′ : Ctx}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ inner′ : RelatedConfiguration Cᴸ Cᴿ′}
    (edge : outer ↘ᶜ inner) (edge′ : outer′ ↘ᶜ inner′) : Set₁ where
  constructor evolve-edge
  field
    same-source-frame : sourceFrame edge ≡ sourceFrame edge′
    target-edge-ready : TargetEdgeReady edge′

open TargetEdgeEvolution


------------------------------------------------------------------------
-- Constructor-form views of the four binary evaluation edges
------------------------------------------------------------------------

data ApplicationLeftEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (source-argument : Term (Δᵉ Cᴸ)) : Set₁ where

  application-left-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {L : Term (Δᵉ Cᴸ)} {L′ M′ : Term (Δᵉ Cᴿ)}
      {A B : Ty (Δᵉ Cᴸ)} {A′ B′ : Ty (Δᵉ Cᴿ)}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² source-argument ⊑ M′ ∶ pA)
    → outer ≡ pack (CTI.·⊑·² function-rel argument-rel)
    → inner ≡ pack function-rel
    → ApplicationLeftEdgeView outer inner source-argument

application-left-edge-view : ∀ {Cᴸ Cᴿ M}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ app-leftᶠ M
  → ApplicationLeftEdgeView outer inner M
application-left-edge-view (focus-·₁ function-rel argument-rel) refl =
  application-left-edge function-rel argument-rel refl refl
application-left-edge-view
    (focus-·₂ function-rel argument-rel source-value) ()
application-left-edge-view (focus-⊕₁ left-rel right-rel r) ()
application-left-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) ()
application-left-edge-view (focus-•-paired p∀ related q r) ()
application-left-edge-view (focus-•-source p∀ related q r) ()
application-left-edge-view (focus-cast-paired c c′ related q) ()
application-left-edge-view (focus-cast-target c′ related q) ()
application-left-edge-view (focus-cast-source c related q) ()
application-left-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) ()
application-left-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) ()
application-left-edge-view
    (focus-source-reveal-identity c⊢ absent related q) ()
application-left-edge-view
    (focus-source-conceal-identity c⊢ absent related q) ()
application-left-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) ()
application-left-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) ()
application-left-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
application-left-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
application-left-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) ()
application-left-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) ()

data ApplicationRightEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (source-function : Term (Δᵉ Cᴸ)) : Set₁ where

  application-right-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {M : Term (Δᵉ Cᴸ)} {L′ M′ : Term (Δᵉ Cᴿ)}
      {A B : Ty (Δᵉ Cᴸ)} {A′ B′ : Ty (Δᵉ Cᴿ)}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      (function-rel : γ CTI.⊢² source-function ⊑ L′ ∶ ⇒⊑⇒ pA pB)
      (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
      (source-value : Value source-function)
      (target-value : Value L′)
    → outer ≡ pack (CTI.·⊑·² function-rel argument-rel)
    → inner ≡ pack argument-rel
    → ApplicationRightEdgeView outer inner source-function

application-right-edge-view : ∀ {Cᴸ Cᴿ L}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ app-rightᶠ L
  → TargetEdgeReady edge
  → ApplicationRightEdgeView outer inner L
application-right-edge-view (focus-·₁ function-rel argument-rel) () ready
application-right-edge-view
    (focus-·₂ function-rel argument-rel source-value) refl target-value =
  application-right-edge function-rel argument-rel source-value target-value
    refl refl
application-right-edge-view (focus-⊕₁ left-rel right-rel r) () ready
application-right-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) () ready
application-right-edge-view (focus-•-paired p∀ related q r) () ready
application-right-edge-view (focus-•-source p∀ related q r) () ready
application-right-edge-view (focus-cast-paired c c′ related q) () ready
application-right-edge-view (focus-cast-target c′ related q) () ready
application-right-edge-view (focus-cast-source c related q) () ready
application-right-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) () ready
application-right-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) () ready
application-right-edge-view
    (focus-source-reveal-identity c⊢ absent related q) () ready
application-right-edge-view
    (focus-source-conceal-identity c⊢ absent related q) () ready
application-right-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) () ready
application-right-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) () ready
application-right-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) () ready
application-right-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) () ready
application-right-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) () ready
application-right-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) () ready

data PrimitiveLeftEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (op : Prim) (source-right : Term (Δᵉ Cᴸ)) : Set₁ where

  primitive-left-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {L : Term (Δᵉ Cᴸ)} {L′ M′ : Term (Δᵉ Cᴿ)}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² source-right ⊑ M′ ∶ q)
      (result-rel :
        primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    → outer ≡ pack (CTI.⊕⊑⊕² op left-rel right-rel result-rel)
    → inner ≡ pack left-rel
    → PrimitiveLeftEdgeView outer inner op source-right

primitive-left-edge-view : ∀ {Cᴸ Cᴿ op M}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ primitive-leftᶠ op M
  → PrimitiveLeftEdgeView outer inner op M
primitive-left-edge-view (focus-·₁ function-rel argument-rel) ()
primitive-left-edge-view
    (focus-·₂ function-rel argument-rel source-value) ()
primitive-left-edge-view (focus-⊕₁ left-rel right-rel r) refl =
  primitive-left-edge left-rel right-rel r refl refl
primitive-left-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) ()
primitive-left-edge-view (focus-•-paired p∀ related q r) ()
primitive-left-edge-view (focus-•-source p∀ related q r) ()
primitive-left-edge-view (focus-cast-paired c c′ related q) ()
primitive-left-edge-view (focus-cast-target c′ related q) ()
primitive-left-edge-view (focus-cast-source c related q) ()
primitive-left-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) ()
primitive-left-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) ()
primitive-left-edge-view
    (focus-source-reveal-identity c⊢ absent related q) ()
primitive-left-edge-view
    (focus-source-conceal-identity c⊢ absent related q) ()
primitive-left-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) ()
primitive-left-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) ()
primitive-left-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
primitive-left-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
primitive-left-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) ()
primitive-left-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) ()

data PrimitiveRightEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (op : Prim) (source-left : Term (Δᵉ Cᴸ)) : Set₁ where

  primitive-right-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {M : Term (Δᵉ Cᴸ)} {L′ M′ : Term (Δᵉ Cᴿ)}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
      (left-rel : γ CTI.⊢² source-left ⊑ L′ ∶ p)
      (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
      (result-rel :
        primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
      (source-value : Value source-left)
      (target-value : Value L′)
    → outer ≡ pack (CTI.⊕⊑⊕² op left-rel right-rel result-rel)
    → inner ≡ pack right-rel
    → PrimitiveRightEdgeView outer inner op source-left

primitive-right-edge-view : ∀ {Cᴸ Cᴿ op L}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ primitive-rightᶠ op L
  → TargetEdgeReady edge
  → PrimitiveRightEdgeView outer inner op L
primitive-right-edge-view (focus-·₁ function-rel argument-rel) () ready
primitive-right-edge-view
    (focus-·₂ function-rel argument-rel source-value) () ready
primitive-right-edge-view (focus-⊕₁ left-rel right-rel r) () ready
primitive-right-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) refl target-value =
  primitive-right-edge left-rel right-rel r source-value target-value
    refl refl
primitive-right-edge-view (focus-•-paired p∀ related q r) () ready
primitive-right-edge-view (focus-•-source p∀ related q r) () ready
primitive-right-edge-view (focus-cast-paired c c′ related q) () ready
primitive-right-edge-view (focus-cast-target c′ related q) () ready
primitive-right-edge-view (focus-cast-source c related q) () ready
primitive-right-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) () ready
primitive-right-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) () ready
primitive-right-edge-view
    (focus-source-reveal-identity c⊢ absent related q) () ready
primitive-right-edge-view
    (focus-source-conceal-identity c⊢ absent related q) () ready
primitive-right-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) () ready
primitive-right-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) () ready
primitive-right-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) () ready
primitive-right-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) () ready
primitive-right-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) () ready
primitive-right-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) () ready

data PairedTypeApplicationEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (source-body : Ty (Nat.suc (Δᵉ Cᴸ)))
    (source-argument : Ty (Δᵉ Cᴸ)) : Set₁ where

  paired-type-application-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ Cᴿ)}
      {target-body : Ty (Nat.suc (Δᵉ Cᴿ))}
      {target-argument : Ty (Δᵉ Cᴿ)}
      (universal-related :
        `∀ source-body ⊑ᵀ⟨ γ ⟩ `∀ target-body)
      (related : γ CTI.⊢² M ⊑ M′ ∶ universal-related)
      (argument-related :
        source-argument ⊑ᵀ⟨ γ ⟩ target-argument)
      (result-related :
        source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γ ⟩
          target-body [ target-argument ]ᵗ)
    → outer ≡ pack
        (CTI.•⊑•² universal-related related argument-related result-related)
    → inner ≡ pack related
    → PairedTypeApplicationEdgeView
        outer inner source-body source-argument

paired-type-application-edge-view : ∀ {Cᴸ Cᴿ C A}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ paired-type-applicationᶠ C A
  → PairedTypeApplicationEdgeView outer inner C A
paired-type-application-edge-view
    (focus-·₁ function-rel argument-rel) ()
paired-type-application-edge-view
    (focus-·₂ function-rel argument-rel source-value) ()
paired-type-application-edge-view
    (focus-⊕₁ left-rel right-rel r) ()
paired-type-application-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) ()
paired-type-application-edge-view
    (focus-•-paired p∀ related q r) refl =
  paired-type-application-edge p∀ related q r refl refl
paired-type-application-edge-view
    (focus-•-source p∀ related q r) ()
paired-type-application-edge-view
    (focus-cast-paired c c′ related q) ()
paired-type-application-edge-view (focus-cast-target c′ related q) ()
paired-type-application-edge-view (focus-cast-source c related q) ()
paired-type-application-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) ()
paired-type-application-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) ()
paired-type-application-edge-view
    (focus-source-reveal-identity c⊢ absent related q) ()
paired-type-application-edge-view
    (focus-source-conceal-identity c⊢ absent related q) ()
paired-type-application-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) ()
paired-type-application-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) ()
paired-type-application-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
paired-type-application-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
paired-type-application-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) ()
paired-type-application-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) ()

data SourceTypeApplicationEdgeView {Cᴸ Cᴿ : Ctx}
    (outer inner : RelatedConfiguration Cᴸ Cᴿ)
    (source-body : Ty (Nat.suc (Δᵉ Cᴸ)))
    (source-argument : Ty (Δᵉ Cᴸ)) : Set₁ where

  source-type-application-edge : ∀
      {γ : Cᴸ ⊑ᶜ Cᴿ}
      {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ Cᴿ)}
      {target-type : Ty (Δᵉ Cᴿ)}
      (universal-related : `∀ source-body ⊑ᵀ⟨ γ ⟩ target-type)
      (related : γ CTI.⊢² M ⊑ M′ ∶ universal-related)
      (argument-related : source-argument ⊑ᵀ⟨ γ ⟩ ★)
      (result-related :
        source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γ ⟩ target-type)
    → outer ≡ pack
        (CTI.•⊑² universal-related related argument-related result-related)
    → inner ≡ pack related
    → SourceTypeApplicationEdgeView
        outer inner source-body source-argument

source-type-application-edge-view : ∀ {Cᴸ Cᴿ C A}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → sourceFrame edge ≡ source-type-applicationᶠ C A
  → SourceTypeApplicationEdgeView outer inner C A
source-type-application-edge-view
    (focus-·₁ function-rel argument-rel) ()
source-type-application-edge-view
    (focus-·₂ function-rel argument-rel source-value) ()
source-type-application-edge-view
    (focus-⊕₁ left-rel right-rel r) ()
source-type-application-edge-view
    (focus-⊕₂ left-rel right-rel r source-value) ()
source-type-application-edge-view
    (focus-•-paired p∀ related q r) ()
source-type-application-edge-view
    (focus-•-source p∀ related q r) refl =
  source-type-application-edge p∀ related q r refl refl
source-type-application-edge-view
    (focus-cast-paired c c′ related q) ()
source-type-application-edge-view (focus-cast-target c′ related q) ()
source-type-application-edge-view (focus-cast-source c related q) ()
source-type-application-edge-view
    (focus-target-reveal-identity c′⊢ absent related q) ()
source-type-application-edge-view
    (focus-target-conceal-identity c′⊢ absent related q) ()
source-type-application-edge-view
    (focus-source-reveal-identity c⊢ absent related q) ()
source-type-application-edge-view
    (focus-source-conceal-identity c⊢ absent related q) ()
source-type-application-edge-view
    (focus-source-reveal-only
      c⊢ present mark free represented related q) ()
source-type-application-edge-view
    (focus-source-conceal-only
      c⊢ present mark free represented related q) ()
source-type-application-edge-view
    (focus-reveal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
source-type-application-edge-view
    (focus-conceal-paired
      c⊢ c′⊢ positions aligned represented related q) ()
source-type-application-edge-view
    (focus-target-reveal-rebase c′⊢ rebase related q) ()
source-type-application-edge-view
    (focus-target-conceal-rebase c′⊢ rebase related q) ()

data TargetPathEvolution {Cᴸ Cᴿ Cᴿ′ : Ctx} :
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ focus′ : RelatedConfiguration Cᴸ Cᴿ′}
    (path : outer ↘ᶜ* focus) (path′ : outer′ ↘ᶜ* focus′) → Set₁ where
  evolve-here : ∀ {related related′}
    → TargetPathEvolution
        (focus-here {related = related}) (focus-here {related = related′})
  evolve-there : ∀ {outer middle focus outer′ middle′ focus′}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
      {edge′ : outer′ ↘ᶜ middle′} {tail′ : middle′ ↘ᶜ* focus′}
    → TargetEdgeEvolution edge edge′
    → TargetPathEvolution tail tail′
    → TargetPathEvolution
        (focus-there edge tail) (focus-there edge′ tail′)

compose-target-edge-evolution : ∀ {Cᴸ Cᴿ₁ Cᴿ₂ Cᴿ₃}
    {outer₁ inner₁ : RelatedConfiguration Cᴸ Cᴿ₁}
    {outer₂ inner₂ : RelatedConfiguration Cᴸ Cᴿ₂}
    {outer₃ inner₃ : RelatedConfiguration Cᴸ Cᴿ₃}
    {edge₁ : outer₁ ↘ᶜ inner₁} {edge₂ : outer₂ ↘ᶜ inner₂}
    {edge₃ : outer₃ ↘ᶜ inner₃}
  → TargetEdgeEvolution edge₁ edge₂
  → TargetEdgeEvolution edge₂ edge₃
  → TargetEdgeEvolution edge₁ edge₃
compose-target-edge-evolution evolution₁ evolution₂ =
  evolve-edge
    (trans (same-source-frame evolution₁)
      (same-source-frame evolution₂))
    (target-edge-ready evolution₂)

compose-target-path-evolution : ∀ {Cᴸ Cᴿ₁ Cᴿ₂ Cᴿ₃}
    {outer₁ focus₁ : RelatedConfiguration Cᴸ Cᴿ₁}
    {outer₂ focus₂ : RelatedConfiguration Cᴸ Cᴿ₂}
    {outer₃ focus₃ : RelatedConfiguration Cᴸ Cᴿ₃}
    {path₁ : outer₁ ↘ᶜ* focus₁} {path₂ : outer₂ ↘ᶜ* focus₂}
    {path₃ : outer₃ ↘ᶜ* focus₃}
  → TargetPathEvolution path₁ path₂
  → TargetPathEvolution path₂ path₃
  → TargetPathEvolution path₁ path₃
compose-target-path-evolution evolve-here evolve-here = evolve-here
compose-target-path-evolution
    (evolve-there edge-evolution₁ path-evolution₁)
    (evolve-there edge-evolution₂ path-evolution₂) =
  evolve-there
    (compose-target-edge-evolution edge-evolution₁ edge-evolution₂)
    (compose-target-path-evolution path-evolution₁ path-evolution₂)

data TargetExtendedPathEvolution {Cᴸ Cᴿ Cᴿ′ : Ctx}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    (path : outer ↘ᶜ* middle) (edge : middle ↘ᶜ focus)
    {outer′ focus′ : RelatedConfiguration Cᴸ Cᴿ′}
    (path′ : outer′ ↘ᶜ* focus′) : Set₁ where
  evolved-extended-path : ∀
      {middle′ : RelatedConfiguration Cᴸ Cᴿ′}
      (prefix′ : outer′ ↘ᶜ* middle′)
      (edge′ : middle′ ↘ᶜ focus′)
    → path′ ≡ extend-focus prefix′ edge′
    → TargetPathEvolution path prefix′
    → TargetEdgeEvolution edge edge′
    → TargetExtendedPathEvolution path edge path′

split-target-extended-path : ∀ {Cᴸ Cᴿ Cᴿ′}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
    {outer′ focus′ : RelatedConfiguration Cᴸ Cᴿ′}
    {path′ : outer′ ↘ᶜ* focus′}
  → TargetPathEvolution (extend-focus path edge) path′
  → TargetExtendedPathEvolution path edge path′
split-target-extended-path {path = focus-here}
    (evolve-there edge-evolution evolve-here) =
  evolved-extended-path focus-here _ refl evolve-here edge-evolution
split-target-extended-path {path = focus-there outer-edge tail}
    (evolve-there outer-evolution tail-evolution)
    with split-target-extended-path tail-evolution
split-target-extended-path {path = focus-there outer-edge tail}
    (evolve-there outer-evolution tail-evolution)
  | evolved-extended-path prefix′ edge′ path-eq prefix-evolution
      edge-evolution =
    evolved-extended-path (focus-there _ prefix′) edge′
      (cong (focus-there _) path-eq)
      (evolve-there outer-evolution prefix-evolution)
      edge-evolution


------------------------------------------------------------------------
-- Target evaluation readiness after focused value catch-up
------------------------------------------------------------------------

TargetReady : ∀ {Cᴸ Cᴿ}
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ* focus → Set
TargetReady focus-here = ⊤
TargetReady (focus-there (focus-·₁ function-rel argument-rel) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-·₂ {L′ = L′} function-rel argument-rel source-value) tail) =
  Value L′ × TargetReady tail
TargetReady (focus-there (focus-⊕₁ left-rel right-rel r) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-⊕₂ {L′ = L′} left-rel right-rel r source-value) tail) =
  Value L′ × TargetReady tail
TargetReady (focus-there (focus-•-paired p∀ related q r) tail) =
  TargetReady tail
TargetReady (focus-there (focus-•-source p∀ related q r) tail) =
  TargetReady tail
TargetReady
    (focus-there (focus-cast-paired c c′ related q) tail) =
  TargetReady tail
TargetReady (focus-there (focus-cast-target c′ related q) tail) =
  TargetReady tail
TargetReady (focus-there (focus-cast-source c related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-target-reveal-identity c′⊢ absent related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-target-conceal-identity c′⊢ absent related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-source-reveal-identity c⊢ absent related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-source-conceal-identity c⊢ absent related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-source-reveal-only c⊢ present mark free represented related q)
      tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-source-conceal-only c⊢ present mark free represented related q)
      tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q)
      tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q)
      tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-target-reveal-rebase c′⊢ rebase related q) tail) =
  TargetReady tail
TargetReady
    (focus-there
      (focus-target-conceal-rebase c′⊢ rebase related q) tail) =
  TargetReady tail

extend-target-ready : ∀ {Cᴸ Cᴿ}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ middle) {tail : middle ↘ᶜ* focus}
  → TargetEdgeReady edge
  → TargetReady tail
  → TargetReady (focus-there edge tail)
extend-target-ready (focus-·₁ function-rel argument-rel) tt ready = ready
extend-target-ready
    (focus-·₂ function-rel argument-rel source-value)
    target-value ready =
  target-value , ready
extend-target-ready (focus-⊕₁ left-rel right-rel r) tt ready = ready
extend-target-ready
    (focus-⊕₂ left-rel right-rel r source-value)
    target-value ready =
  target-value , ready
extend-target-ready (focus-•-paired p∀ related q r) tt ready = ready
extend-target-ready (focus-•-source p∀ related q r) tt ready = ready
extend-target-ready (focus-cast-paired c c′ related q) tt ready = ready
extend-target-ready (focus-cast-target c′ related q) tt ready = ready
extend-target-ready (focus-cast-source c related q) tt ready = ready
extend-target-ready
    (focus-target-reveal-identity c′⊢ absent related q) tt ready =
  ready
extend-target-ready
    (focus-target-conceal-identity c′⊢ absent related q) tt ready =
  ready
extend-target-ready
    (focus-source-reveal-identity c⊢ absent related q) tt ready =
  ready
extend-target-ready
    (focus-source-conceal-identity c⊢ absent related q) tt ready =
  ready
extend-target-ready
    (focus-source-reveal-only c⊢ present mark free represented related q)
    tt ready =
  ready
extend-target-ready
    (focus-source-conceal-only c⊢ present mark free represented related q)
    tt ready =
  ready
extend-target-ready
    (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q)
    tt ready =
  ready
extend-target-ready
    (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q)
    tt ready =
  ready
extend-target-ready
    (focus-target-reveal-rebase c′⊢ rebase related q) tt ready =
  ready
extend-target-ready
    (focus-target-conceal-rebase c′⊢ rebase related q) tt ready =
  ready

target-path-ready : ∀ {Cᴸ Cᴿ Cᴿ′}
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ focus′ : RelatedConfiguration Cᴸ Cᴿ′}
    {path : outer ↘ᶜ* focus} {path′ : outer′ ↘ᶜ* focus′}
  → TargetPathEvolution path path′
  → TargetReady path′
target-path-ready evolve-here = tt
target-path-ready (evolve-there edge-evolution path-evolution) =
  extend-target-ready _ (target-edge-ready edge-evolution)
    (target-path-ready path-evolution)


------------------------------------------------------------------------
-- Source reduct reconstruction through the zipper
------------------------------------------------------------------------

rebuildSourceEdge : ∀ {Cᴸ Cᴿ Δᴸ′}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner
  → StoreChange (Δᵉ Cᴸ) Δᴸ′
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

data RebuildSourceEdge {Cᴸ Cᴿ : Ctx} {Δᴸ′ : TyCtx}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
    (χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′)
    (inner-result : Term Δᴸ′) : Term Δᴸ′ → Set where

  rebuild-edge : ∀ {outer-result}
    → outer-result ≡ rebuildSourceEdge edge χᴸ inner-result
    → RebuildSourceEdge edge χᴸ inner-result outer-result

data RebuildSource {Cᴸ Cᴿ : Ctx} {Δᴸ′ : TyCtx} :
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    → (path : outer ↘ᶜ* focus)
    → (χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′)
    → (focus-result : Term Δᴸ′)
    → Term Δᴸ′ → Set₁ where

  rebuild-here : ∀ {related : RelatedConfiguration Cᴸ Cᴿ}
      {χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′}
      {focus-result result : Term Δᴸ′}
    → result ≡ focus-result
    → RebuildSource {outer = related} {focus = related}
        focus-here χᴸ focus-result result

  rebuild-there : ∀
      {outer focus middle : RelatedConfiguration Cᴸ Cᴿ}
      {χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′}
      {focus-result middle-result outer-result : Term Δᴸ′}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
    → RebuildSource tail χᴸ focus-result middle-result
    → RebuildSourceEdge edge χᴸ middle-result outer-result
    → RebuildSource (focus-there edge tail) χᴸ focus-result outer-result

extend-rebuild : ∀ {Cᴸ Cᴿ Δᴸ′}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
    {χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′}
    {focus-result middle-result outer-result : Term Δᴸ′}
  → RebuildSource path χᴸ middle-result outer-result
  → RebuildSourceEdge edge χᴸ focus-result middle-result
  → RebuildSource (extend-focus path edge) χᴸ focus-result outer-result
extend-rebuild (rebuild-here refl) edge-rebuild =
  rebuild-there (rebuild-here refl) edge-rebuild
extend-rebuild (rebuild-there tail-rebuild outer-rebuild) edge-rebuild =
  rebuild-there (extend-rebuild tail-rebuild edge-rebuild) outer-rebuild

source-frame-rebuild : ∀ {Cᴸ Cᴿ Δᴸ′}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner) (χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′)
    (P : Term Δᴸ′)
  → rebuildSourceEdge edge χᴸ P ≡ rebuildFrame (sourceFrame edge) χᴸ P
source-frame-rebuild (focus-·₁ function-rel argument-rel) χᴸ P = refl
source-frame-rebuild
    (focus-·₂ function-rel argument-rel source-value) χᴸ P = refl
source-frame-rebuild (focus-⊕₁ left-rel right-rel r) χᴸ P = refl
source-frame-rebuild
    (focus-⊕₂ left-rel right-rel r source-value) χᴸ P = refl
source-frame-rebuild (focus-•-paired p∀ related q r) χᴸ P = refl
source-frame-rebuild (focus-•-source p∀ related q r) χᴸ P = refl
source-frame-rebuild (focus-cast-paired c c′ related q) χᴸ P = refl
source-frame-rebuild (focus-cast-target c′ related q) χᴸ P = refl
source-frame-rebuild (focus-cast-source c related q) χᴸ P = refl
source-frame-rebuild
    (focus-target-reveal-identity c′⊢ absent related q) χᴸ P = refl
source-frame-rebuild
    (focus-target-conceal-identity c′⊢ absent related q) χᴸ P = refl
source-frame-rebuild
    (focus-source-reveal-identity c⊢ absent related q) χᴸ P = refl
source-frame-rebuild
    (focus-source-conceal-identity c⊢ absent related q) χᴸ P = refl
source-frame-rebuild
    (focus-source-reveal-only c⊢ present mark free represented related q)
    χᴸ P = refl
source-frame-rebuild
    (focus-source-conceal-only c⊢ present mark free represented related q)
    χᴸ P = refl
source-frame-rebuild
    (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q)
    χᴸ P = refl
source-frame-rebuild
    (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q)
    χᴸ P = refl
source-frame-rebuild
    (focus-target-reveal-rebase c′⊢ rebase related q) χᴸ P = refl
source-frame-rebuild
    (focus-target-conceal-rebase c′⊢ rebase related q) χᴸ P = refl

edge-rebuild-equality : ∀ {Cᴸ Cᴿ Cᴿ′ Δᴸ′}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ inner′ : RelatedConfiguration Cᴸ Cᴿ′}
    {edge : outer ↘ᶜ inner} {edge′ : outer′ ↘ᶜ inner′}
  → TargetEdgeEvolution edge edge′
  → (χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′)
  → (P : Term Δᴸ′)
  → rebuildSourceEdge edge χᴸ P ≡ rebuildSourceEdge edge′ χᴸ P
edge-rebuild-equality {edge = edge} {edge′ = edge′} evolution χᴸ P =
  trans (source-frame-rebuild edge χᴸ P)
    (trans
      (cong (λ frame → rebuildFrame frame χᴸ P)
        (same-source-frame evolution))
      (sym (source-frame-rebuild edge′ χᴸ P)))

transport-rebuild : ∀ {Cᴸ Cᴿ Cᴿ′ Δᴸ′}
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ focus′ : RelatedConfiguration Cᴸ Cᴿ′}
    {path : outer ↘ᶜ* focus} {path′ : outer′ ↘ᶜ* focus′}
    {χᴸ : StoreChange (Δᵉ Cᴸ) Δᴸ′} {P N : Term Δᴸ′}
  → TargetPathEvolution path path′
  → RebuildSource path χᴸ P N
  → RebuildSource path′ χᴸ P N
transport-rebuild evolve-here (rebuild-here refl) = rebuild-here refl
transport-rebuild (evolve-there edge-evolution path-evolution)
    (rebuild-there tail-rebuild (rebuild-edge outer-eq)) =
  rebuild-there (transport-rebuild path-evolution tail-rebuild)
    (rebuild-edge
      (trans outer-eq
        (edge-rebuild-equality edge-evolution _ _)))


------------------------------------------------------------------------
-- One selected target reveal/rebase inside a whole caller path
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

extend-selected-reveal : ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
    {c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′}
    {rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ}
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    {related : γᵖ CTI.⊢² M ⊑ M′ ∶ p}
    {q : A ⊑ᵀ⟨ γ ⟩ B′}
    {outer middle focus : RelatedConfiguration
      (⟨ Δᴸ , Σᴸ , Γᴸ ⟩) (⟨ Δᴿ , Σᴿ , Γᴿ ⟩)}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
  → TargetRevealRebaseInPath c′⊢ rebase related q path
  → TargetRevealRebaseInPath c′⊢ rebase related q
      (extend-focus path edge)
extend-selected-reveal selected-here = selected-here
extend-selected-reveal (selected-there selected) =
  selected-there (extend-selected-reveal selected)


------------------------------------------------------------------------
-- Whole-caller target reveal/rebase closing
------------------------------------------------------------------------

WholeContextualTargetRevealRebaseClosingᵀ : Set₁
WholeContextualTargetRevealRebaseClosingᵀ = ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γʳᵒᵒᵗ γ γᵖ :
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {root-source : Term Δᴸ} {root-target : Term Δᴿ}
    {root-result : Term Δᴸ′}
    {root-source-type : Ty Δᴸ} {root-target-type : Ty Δᴿ}
    {root-type-related :
      root-source-type ⊑ᵀ⟨ γʳᵒᵒᵗ ⟩ root-target-type}
  → openFramesᶜ γʳᵒᵒᵗ ≡ []
  → (root-related : γʳᵒᵒᵗ CTI.⊢² root-source ⊑ root-target ∶
      root-type-related)
  → ∀ {inner-source : Term Δᴸ} {inner-target : Term Δᴿ}
      {inner-source-type : Ty Δᴸ}
      {inner-target-type selected-target-type Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {target-reveal : Conv↑ Δᴿ inner-target-type selected-target-type}
  → (target-reveal⊢ :
      Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] target-reveal)
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
          {W = γʳᵒᵒᵗ} {W′ = γ′} (χᴸ ∷ˢ []ˢ) χsᴿ
      × (γ′ CTI.⊢² root-result ⊑ N′ ∶ final-related)


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
  → ∀ {γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
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

whole-closing-specializes-to-contextual :
    WholeContextualTargetRevealRebaseClosingᵀ
  → ContextualTargetRevealRebaseClosingᵀ
whole-closing-specializes-to-contextual close no-open target-reveal⊢
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

contextual-closing-adapter :
    ContextualTargetRevealRebaseClosingᵀ
  → SimTargetRevealRebaseClosingᵀ
contextual-closing-adapter close no-open c′⊢ rebase related q step =
  close no-open c′⊢ rebase related q related focus-here step
    (rebuild-here refl)
