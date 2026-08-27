{-# OPTIONS --safe #-}

module proof.DGG.notes.AlignmentOnlyEvolutionProjectionProbe where

-- File Charter:
--   * Checks the type and open-frame projections needed by the proposed
--     source-bind-plus-alignment WorldEvolution constructor.
--   * Keeps the live evolution relation unchanged while stage 1 migrates the
--     role-tagged World construction sites.
--   * Confirms that shifted source types do not observe a rebase at zero and
--     that the alignment-only node contributes no open frame.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types using
  (Ty; TyVar; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-comp; renameᵗ-cong)
open import TyStore using (TyStore; lookupStore)
open import Imprecision using (_⊢_⊑_)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (⟨_,_,_⟩)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-bind-left; evolution-⊑ᵀ)


rename-shifted-off-zero : ∀ {Δᴸ Δᶜ}
    {η : Injectionᵗ (suc Δᴸ) Δᶜ}
    {Z : TyVar Δᶜ}
  → (update : PivotUpdateᵗ η Fin.zero Z)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameⁱ (pivot-afterᵗ update)) (⇑ᵗ A)
    ≡ renameᵗ (toRenameⁱ η) (⇑ᵗ A)
rename-shifted-off-zero {η = η} update A =
  trans (renameᵗ-comp Fin.suc
      (toRenameⁱ (pivot-afterᵗ update)) A)
    (trans
      (renameᵗ-cong A
        (λ X → off-pivot-fixedᵗ update (Fin.suc X) (λ ())))
      (sym (renameᵗ-comp Fin.suc (toRenameⁱ η) A)))


aligned-source-bind-⊑ᵀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴿ : TyVar Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → (update : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
      (toRenameⁱ
        (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
  → (boundary : AlignmentBoundaryᶜ
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
  → (represented :
      (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
        lookupStore Σᴿ Xᴿ)
  → A ⊑ᵀ⟨ γ ⟩ B
  → ⇑ᵗ A ⊑ᵀ⟨
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
        rebase-source-changeᶜ Fin.zero Xᴿ update
          (alignment-onlyᶜ boundary) represented
      ⟩ B
aligned-source-bind-⊑ᵀ {C = C} {γ = γ} {A = A} {B = B}
    eqᴸ update boundary represented p =
  subst
    (λ L → marksᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢ L ⊑
      renameᵗ
        (toRenameⁱ (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ))) B)
    (sym (rename-shifted-off-zero update A))
    (evolution-⊑ᵀ
      (evolution-bind-left {A = C} {W = γ} eqᴸ) p)


aligned-source-bind-open-frames : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴿ : TyVar Δᴿ}
  → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → (update : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
      (toRenameⁱ
        (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
  → (boundary : AlignmentBoundaryᶜ
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
  → (represented :
      (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
        lookupStore Σᴿ Xᴿ)
  → openFramesᶜ
      ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
        rebase-source-changeᶜ Fin.zero Xᴿ update
          (alignment-onlyᶜ boundary) represented)
    ≡ renameOpenFramesᶜ Fin.suc (λ X → X) (openFramesᶜ γ)
aligned-source-bind-open-frames eqᴸ update boundary represented = refl


aligned-source-bind-aligned : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴿ : TyVar Δᴿ} {Yᴸ : TyVar Δᴸ} {Yᴿ : TyVar Δᴿ}
  → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → (update : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
      (toRenameⁱ
        (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
  → (boundary : AlignmentBoundaryᶜ
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
  → (represented :
      (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
        lookupStore Σᴿ Xᴿ)
  → toRenameⁱ (ηᴸᶜ γ) Yᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Yᴿ
  → toRenameⁱ
      (ηᴸᶜ
        ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
          rebase-source-changeᶜ Fin.zero Xᴿ update
            (alignment-onlyᶜ boundary) represented))
      (Fin.suc Yᴸ)
    ≡ toRenameⁱ
      (ηᴿᶜ
        ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
          rebase-source-changeᶜ Fin.zero Xᴿ update
            (alignment-onlyᶜ boundary) represented))
      Yᴿ
aligned-source-bind-aligned {Yᴸ = Yᴸ}
    eqᴸ update boundary represented aligned =
  trans (off-pivot-fixedᵗ update (Fin.suc Yᴸ) (λ ()))
    (cong Fin.suc aligned)


aligned-source-bind-source-mark : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴿ : TyVar Δᴿ} {Yᴸ : TyVar Δᴸ} {v}
  → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → (update : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
      (toRenameⁱ
        (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
  → (boundary : AlignmentBoundaryᶜ
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
  → (represented :
      (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
        lookupStore Σᴿ Xᴿ)
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Yᴸ) ≡ v
  → marksᶜ
      ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
        rebase-source-changeᶜ Fin.zero Xᴿ update
          (alignment-onlyᶜ boundary) represented)
      (toRenameⁱ
        (ηᴸᶜ
          ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
            rebase-source-changeᶜ Fin.zero Xᴿ update
              (alignment-onlyᶜ boundary) represented))
        (Fin.suc Yᴸ))
    ≡ v
aligned-source-bind-source-mark {C = C} {γ = γ} {Yᴸ = Yᴸ}
    eqᴸ update boundary represented mark =
  trans
    (cong (marksᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ))
      (off-pivot-fixedᵗ update (Fin.suc Yᴸ) (λ ())))
    mark


aligned-source-bind-source-disaligned : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴿ : TyVar Δᴿ} {Yᴸ : TyVar Δᴸ}
  → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → (update : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
      (toRenameⁱ
        (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
  → (boundary : AlignmentBoundaryᶜ
      (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
  → (represented :
      (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
        lookupStore Σᴿ Xᴿ)
  → (∀ Yᴿ → toRenameⁱ (ηᴿᶜ γ) Yᴿ
      ≢ toRenameⁱ (ηᴸᶜ γ) Yᴸ)
  → ∀ Yᴿ → toRenameⁱ
      (ηᴿᶜ
        ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
          rebase-source-changeᶜ Fin.zero Xᴿ update
            (alignment-onlyᶜ boundary) represented)) Yᴿ
      ≢ toRenameⁱ
        (ηᴸᶜ
          ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
            rebase-source-changeᶜ Fin.zero Xᴿ update
              (alignment-onlyᶜ boundary) represented))
        (Fin.suc Yᴸ)
aligned-source-bind-source-disaligned {Yᴸ = Yᴸ}
    eqᴸ update boundary represented free Yᴿ aligned =
  free Yᴿ
    (fin-suc-injectiveⁱ
      (trans aligned
        (off-pivot-fixedᵗ update (Fin.suc Yᴸ) (λ ()))))
