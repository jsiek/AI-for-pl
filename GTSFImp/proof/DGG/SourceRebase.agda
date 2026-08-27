{-# OPTIONS --safe #-}

module proof.DGG.SourceRebase where

-- File Charter:
--   * Defines the source-rebase relation between two worlds with the same
--     endpoint contexts.
--   * Records a direct source rebase and closes that rebase under matching
--     endpoint-indexed world evolution.
--   * Keeps transported pivot indices in constructor form by recording their
--     executable-renaming equations as premises.
--   * Exports no compatibility equality or action wrapper; depends only on
--     World and WorldEvolution.

import Data.Fin as Fin
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans)

open import Types using (Ty; TyVar; ★; ＇_; ⇑ᵗ)
open import TyStore using (TyStore; lookupStore)
import TermCtx as TC
open import TermCtx using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ)

open import proof.DGG.World
open import proof.DGG.WorldEvolution


data SourceRebaseᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → Γᴸ ⊑ᶜ Γᴿ
    → TyVar (Δᵉ Γᴸ)
    → TyVar (Δᵉ Γᴿ)
    → Set where

  source-rebase-now : ∀ {Γᴸ Γᴿ}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
      (ok : PivotUpdateᵗ
        (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ))
      (represented :
        (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ)
    → SourceRebaseᶜ γ
        (γ ▻ᶜ rebase-source-changeᶜ
          Xᴸ Xᴿ ok represented)
        Xᴸ Xᴿ

  source-rebase-bind-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ Xᴿ}
    → (A : Ty Δᴸ)
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸᵖ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → SourceRebaseᶜ
        (γ ▻ᶜ bind-left-changeᶜ A eqᴸ)
        (γᵖ ▻ᶜ bind-left-changeᶜ A eqᴸᵖ)
        (Fin.suc Xᴸ) Xᴿ

  source-rebase-bind-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ Xᴿ}
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → (fresh : RightBindFreshᶜ γ B)
    → (freshᵖ : RightBindFreshᶜ γᵖ B)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿᵖ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseᶜ
        (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ)
        (γᵖ ▻ᶜ bind-right-changeᶜ B freshᵖ eqᴿᵖ)
        Xᴸ (Fin.suc Xᴿ)

  source-rebase-bind-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ Xᴿ}
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (representedᵖ : A ⊑ᵀ⟨ γᵖ ⟩ B)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸᵖ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿᵖ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseᶜ
        (γ ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ)
        (γᵖ ▻ᶜ
          bind-both-changeᶜ representedᵖ eqᴸᵖ eqᴿᵖ)
        (Fin.suc Xᴸ) (Fin.suc Xᴿ)

  source-rebase-bind-both-star : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ Xᴿ}
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (representedᵖ : A ⊑ᵀ⟨ γᵖ ⟩ B)
    → (A≠★ : ⇑ᵗ A ≢ ★)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸᵖ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿᵖ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseᶜ
        (γ ▻ᶜ bind-both-star-changeᶜ
          represented A≠★ eqᴸ eqᴿ)
        (γᵖ ▻ᶜ bind-both-star-changeᶜ
          representedᵖ A≠★ eqᴸᵖ eqᴿᵖ)
        (Fin.suc Xᴸ) (Fin.suc Xᴿ)


source-rebase-can : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → PivotUpdateᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)
source-rebase-can (source-rebase-now ok represented) = ok
source-rebase-can
    (source-rebase-bind-left A rebase eqᴸ eqᴸᵖ) =
  pivotUpdate-keepᵗ (source-rebase-can rebase)
source-rebase-can
    (source-rebase-bind-right rebase fresh freshᵖ eqᴿ eqᴿᵖ) =
  pivotUpdate-skipᵗ (source-rebase-can rebase)
source-rebase-can
    (source-rebase-bind-both rebase represented representedᵖ
      eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  pivotUpdate-keepᵗ (source-rebase-can rebase)
source-rebase-can
    (source-rebase-bind-both-star rebase represented representedᵖ
      A≠★ eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  pivotUpdate-keepᵗ (source-rebase-can rebase)


source-rebase-represented : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ
source-rebase-represented
    (source-rebase-now ok represented) = represented
source-rebase-represented
    (source-rebase-bind-left {γ = γ} A rebase eqᴸ eqᴸᵖ) =
  evolution-source-represented
    {W = γ}
    (evolution-bind-left {A = A} eqᴸ)
    (source-rebase-represented rebase)
source-rebase-represented
    (source-rebase-bind-right {γ = γ}
      rebase fresh freshᵖ eqᴿ eqᴿᵖ) =
  evolution-source-represented
    {W = γ}
    (evolution-bind-right fresh eqᴿ)
    (source-rebase-represented rebase)
source-rebase-represented
    (source-rebase-bind-both {γ = γ} rebase represented representedᵖ
      eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  evolution-source-represented
    {W = γ}
    (evolution-bind-both represented eqᴸ eqᴿ)
    (source-rebase-represented rebase)
source-rebase-represented
    (source-rebase-bind-both-star {γ = γ} rebase represented representedᵖ
      A≠★ eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  evolution-source-represented
    {W = γ}
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ)
    (source-rebase-represented rebase)


source-rebase-center : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → centerᶜ γ ≡ centerᶜ γᵖ
source-rebase-center (source-rebase-now ok represented) = refl
source-rebase-center
    (source-rebase-bind-left A rebase eqᴸ eqᴸᵖ) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-bind-right rebase fresh freshᵖ eqᴿ eqᴿᵖ) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-bind-both rebase represented representedᵖ
      eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-bind-both-star rebase represented representedᵖ
      A≠★ eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  cong suc (source-rebase-center rebase)


source-rebase-count : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → sourceRebaseCountᶜ γᵖ ≡ suc (sourceRebaseCountᶜ γ)
source-rebase-count (source-rebase-now ok represented) = refl
source-rebase-count
    (source-rebase-bind-left A rebase eqᴸ eqᴸᵖ) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-bind-right rebase fresh freshᵖ eqᴿ eqᴿᵖ) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-bind-both rebase represented representedᵖ
      eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-bind-both-star rebase represented representedᵖ
      A≠★ eqᴸ eqᴸᵖ eqᴿ eqᴿᵖ) =
  source-rebase-count rebase


source-rebase-count≢zero : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → sourceRebaseCountᶜ γᵖ ≢ zero
source-rebase-count≢zero rebase eq
    with trans (sym (source-rebase-count rebase)) eq
source-rebase-count≢zero rebase eq | ()
