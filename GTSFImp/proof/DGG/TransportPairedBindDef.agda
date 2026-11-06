{-# OPTIONS --safe #-}

module proof.DGG.TransportPairedBindDef where

-- File Charter:
--   * Defines paired allocation through term and type scope.
--   * Shares one structural scope graph between precise and dynamic roots.
--   * Derives both endpoint renamings and the induced type imprecision.
--   * States only the source-rebase commutations requiring separate proof.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Types using
  (Ty; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-comp; renameᵗ-cong)
open import Imprecision using (X⊑X; _⊢_⊑_)
open import Consistency using
  (_↪ᵗ_; toRenameᵗ; wk↪ᵗ; keep)
open import TyStore using (TyStore; lookupStore)
import TermCtx as TC
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using
  (Term; ⟨_,_,_⟩; renameᵗᵐ; _↑_; _↓_)

open import proof.DGG.World
open import proof.DGG.SourceRebase
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-wk-bind; StoreRename-keep;
   toRename-wk-eq; toRename-id-eq; renameCtx-wk-eq;
   renameCtx-keep-shift)


data PairedBindScope : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
  → (ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺)
  → (ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩)
  → Set where

  paired-scope-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
    → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
    → PairedBindScope wk↪ᵗ wk↪ᵗ γ
        (γ ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ)

  paired-star-scope-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (A≢★ : ⇑ᵗ A ≢ ★)
    → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
    → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
    → PairedBindScope wk↪ᵗ wk↪ᵗ γ
        (γ ▻ᶜ bind-both-star-changeᶜ represented A≢★ eqᴸ eqᴿ)

  paired-scope-term : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : renameᵗ (toRenameᵗ ρᴸ) A ⊑ᵀ⟨ γ⁺ ⟩
        renameᵗ (toRenameᵗ ρᴿ) B)
    → PairedBindScope ρᴸ ρᴿ
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)

  paired-scope-both : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → PairedBindScope ρᴸ ρᴿ γ γ⁺
    → PairedBindScope (keep ρᴸ) (keep ρᴿ)
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γ⁺)

  paired-scope-left : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → PairedBindScope ρᴸ ρᴿ γ γ⁺
    → PairedBindScope (keep ρᴸ) ρᴿ
        (liftLeftᶜ γ) (liftLeftᶜ γ⁺)


paired-scope-center : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindScope ρᴸ ρᴿ γ γ⁺
  → centerᶜ γ ↪ᵗ centerᶜ γ⁺
paired-scope-center (paired-scope-root represented eqᴸ eqᴿ) = wk↪ᵗ
paired-scope-center
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) = wk↪ᵗ
paired-scope-center (paired-scope-term plan p p⁺) =
  paired-scope-center plan
paired-scope-center (paired-scope-both plan) =
  keep (paired-scope-center plan)
paired-scope-center (paired-scope-left plan) =
  keep (paired-scope-center plan)


paired-scope-left-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → ∀ X
  → toRenameᵗ (paired-scope-center plan)
      (toRenameⁱ (ηᴸᶜ γ) X)
    ≡ toRenameⁱ (ηᴸᶜ γ⁺) (toRenameᵗ ρᴸ X)
paired-scope-left-commutes {γ = γ}
    (paired-scope-root represented eqᴸ eqᴿ) X =
  trans (toRename-wk-eq (toRenameⁱ (ηᴸᶜ γ) X))
    (sym (cong (toRenameⁱ (keepⁱ (ηᴸᶜ γ)))
      (toRename-wk-eq X)))
paired-scope-left-commutes {γ = γ}
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) X =
  trans (toRename-wk-eq (toRenameⁱ (ηᴸᶜ γ) X))
    (sym (cong (toRenameⁱ (keepⁱ (ηᴸᶜ γ)))
      (toRename-wk-eq X)))
paired-scope-left-commutes (paired-scope-term plan p p⁺) X =
  paired-scope-left-commutes plan X
paired-scope-left-commutes (paired-scope-both plan) Fin.zero = refl
paired-scope-left-commutes (paired-scope-both plan) (Fin.suc X) =
  cong Fin.suc (paired-scope-left-commutes plan X)
paired-scope-left-commutes (paired-scope-left plan) Fin.zero = refl
paired-scope-left-commutes (paired-scope-left plan) (Fin.suc X) =
  cong Fin.suc (paired-scope-left-commutes plan X)


paired-scope-right-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → ∀ Y
  → toRenameᵗ (paired-scope-center plan)
      (toRenameⁱ (ηᴿᶜ γ) Y)
    ≡ toRenameⁱ (ηᴿᶜ γ⁺) (toRenameᵗ ρᴿ Y)
paired-scope-right-commutes {γ = γ}
    (paired-scope-root represented eqᴸ eqᴿ) Y =
  trans (toRename-wk-eq (toRenameⁱ (ηᴿᶜ γ) Y))
    (sym (cong (toRenameⁱ (keepⁱ (ηᴿᶜ γ)))
      (toRename-wk-eq Y)))
paired-scope-right-commutes {γ = γ}
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) Y =
  trans (toRename-wk-eq (toRenameⁱ (ηᴿᶜ γ) Y))
    (sym (cong (toRenameⁱ (keepⁱ (ηᴿᶜ γ)))
      (toRename-wk-eq Y)))
paired-scope-right-commutes (paired-scope-term plan p p⁺) Y =
  paired-scope-right-commutes plan Y
paired-scope-right-commutes (paired-scope-both plan) Fin.zero = refl
paired-scope-right-commutes (paired-scope-both plan) (Fin.suc Y) =
  cong Fin.suc (paired-scope-right-commutes plan Y)
paired-scope-right-commutes (paired-scope-left plan) Y =
  cong Fin.suc (paired-scope-right-commutes plan Y)


paired-scope-mark : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → ∀ Z
  → marksᶜ γ⁺ (toRenameᵗ (paired-scope-center plan) Z)
    ≡ marksᶜ γ Z
paired-scope-mark {γ = γ}
    (paired-scope-root represented eqᴸ eqᴿ) Z =
  cong (marksᶜ γ) (toRename-id-eq Z)
paired-scope-mark {γ = γ}
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) Z =
  cong (marksᶜ γ) (toRename-id-eq Z)
paired-scope-mark (paired-scope-term plan p p⁺) Z =
  paired-scope-mark plan Z
paired-scope-mark (paired-scope-both plan) Fin.zero = refl
paired-scope-mark (paired-scope-both plan) (Fin.suc Z) =
  paired-scope-mark plan Z
paired-scope-mark (paired-scope-left plan) Fin.zero = refl
paired-scope-mark (paired-scope-left plan) (Fin.suc Z) =
  paired-scope-mark plan Z


paired-scope-source-context : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindScope ρᴸ ρᴿ γ γ⁺
  → Γᴸ⁺ ≡ TC.renameCtx (toRenameᵗ ρᴸ) Γᴸ
paired-scope-source-context (paired-scope-root represented eqᴸ eqᴿ) =
  trans eqᴸ (sym (renameCtx-wk-eq _))
paired-scope-source-context
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) =
  trans eqᴸ (sym (renameCtx-wk-eq _))
paired-scope-source-context (paired-scope-term plan p p⁺) =
  cong₂ _∷_ refl (paired-scope-source-context plan)
paired-scope-source-context (paired-scope-both {Γᴸ = Γᴸ} plan) =
  trans (cong ⇑ᶜ (paired-scope-source-context plan))
    (sym (renameCtx-keep-shift _ Γᴸ))
paired-scope-source-context (paired-scope-left {Γᴸ = Γᴸ} plan) =
  trans (cong ⇑ᶜ (paired-scope-source-context plan))
    (sym (renameCtx-keep-shift _ Γᴸ))


paired-scope-target-context : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindScope ρᴸ ρᴿ γ γ⁺
  → Γᴿ⁺ ≡ TC.renameCtx (toRenameᵗ ρᴿ) Γᴿ
paired-scope-target-context (paired-scope-root represented eqᴸ eqᴿ) =
  trans eqᴿ (sym (renameCtx-wk-eq _))
paired-scope-target-context
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) =
  trans eqᴿ (sym (renameCtx-wk-eq _))
paired-scope-target-context (paired-scope-term plan p p⁺) =
  cong₂ _∷_ refl (paired-scope-target-context plan)
paired-scope-target-context (paired-scope-both {Γᴿ = Γᴿ} plan) =
  trans (cong ⇑ᶜ (paired-scope-target-context plan))
    (sym (renameCtx-keep-shift _ Γᴿ))
paired-scope-target-context (paired-scope-left plan) =
  paired-scope-target-context plan


paired-scope-source-store : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindScope ρᴸ ρᴿ γ γ⁺
  → StoreRename (toRenameᵗ ρᴸ) Σᴸ Σᴸ⁺
paired-scope-source-store (paired-scope-root represented eqᴸ eqᴿ) =
  StoreRename-wk-bind
paired-scope-source-store
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) =
  StoreRename-wk-bind
paired-scope-source-store (paired-scope-term plan p p⁺) =
  paired-scope-source-store plan
paired-scope-source-store (paired-scope-both plan) =
  StoreRename-keep (paired-scope-source-store plan)
paired-scope-source-store (paired-scope-left plan) =
  StoreRename-keep (paired-scope-source-store plan)


paired-scope-target-store : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindScope ρᴸ ρᴿ γ γ⁺
  → StoreRename (toRenameᵗ ρᴿ) Σᴿ Σᴿ⁺
paired-scope-target-store (paired-scope-root represented eqᴸ eqᴿ) =
  StoreRename-wk-bind
paired-scope-target-store
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) =
  StoreRename-wk-bind
paired-scope-target-store (paired-scope-term plan p p⁺) =
  paired-scope-target-store plan
paired-scope-target-store (paired-scope-both plan) =
  StoreRename-keep (paired-scope-target-store plan)
paired-scope-target-store (paired-scope-left plan) =
  paired-scope-target-store plan


paired-scope-source-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameᵗ (paired-scope-center plan))
      (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A)
    ≡ renameᵗ (toRenameⁱ (ηᴸᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴸ) A)
paired-scope-source-type {ρᴸ = ρᴸ} {γ = γ} {γ⁺ = γ⁺} plan A =
  trans
    (renameᵗ-comp (toRenameⁱ (ηᴸᶜ γ))
      (toRenameᵗ (paired-scope-center plan)) A)
    (trans
      (renameᵗ-cong A (paired-scope-left-commutes plan))
      (sym (renameᵗ-comp (toRenameᵗ ρᴸ)
        (toRenameⁱ (ηᴸᶜ γ⁺)) A)))


paired-scope-target-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (paired-scope-center plan))
      (renameᵗ (toRenameⁱ (ηᴿᶜ γ)) B)
    ≡ renameᵗ (toRenameⁱ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴿ) B)
paired-scope-target-type {ρᴿ = ρᴿ} {γ = γ} {γ⁺ = γ⁺} plan B =
  trans
    (renameᵗ-comp (toRenameⁱ (ηᴿᶜ γ))
      (toRenameᵗ (paired-scope-center plan)) B)
    (trans
      (renameᵗ-cong B (paired-scope-right-commutes plan))
      (sym (renameᵗ-comp (toRenameᵗ ρᴿ)
        (toRenameⁱ (ηᴿᶜ γ⁺)) B)))


paired-scope-⊑ᵀ : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → A ⊑ᵀ⟨ γ ⟩ B
  → renameᵗ (toRenameᵗ ρᴸ) A ⊑ᵀ⟨ γ⁺ ⟩
      renameᵗ (toRenameᵗ ρᴿ) B
paired-scope-⊑ᵀ {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ = γ} {γ⁺ = γ⁺}
    {A = A} {B = B} plan p =
  subst (λ L → marksᶜ γ⁺ ⊢ L ⊑
      renameᵗ (toRenameⁱ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴿ) B))
    (paired-scope-source-type plan A)
    (subst (λ R → marksᶜ γ⁺ ⊢
        renameᵗ (toRenameᵗ (paired-scope-center plan))
          (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A) ⊑ R)
      (paired-scope-target-type plan B)
      (rename-⊑
        (toRenameᵗ (paired-scope-center plan))
        (toRenameᵗ-injective (paired-scope-center plan))
        (λ Z mark → trans (paired-scope-mark plan Z) mark)
        p))


TransportPairedBindScopeᵀ : Set
TransportPairedBindScopeᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ⁺ ⊢² renameᵗᵐ ρᴸ M ⊑ renameᵗᵐ ρᴿ M′
      ∶ paired-scope-⊑ᵀ plan p


TransportPairedBindRevealRebaseᵀ : Set
TransportPairedBindRevealRebaseᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → γ⁺ ⊢² renameᵗᵐ ρᴸ M ⊑ renameᵗᵐ ρᴿ (M′ ↑ c′)
      ∶ paired-scope-⊑ᵀ plan q


TransportPairedBindConcealRebaseᵀ : Set
TransportPairedBindConcealRebaseᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↓ Δᴿ B B′}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
  → {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → γ⁺ ⊢² renameᵗᵐ ρᴸ M ⊑ renameᵗᵐ ρᴿ (M′ ↓ c′)
      ∶ paired-scope-⊑ᵀ plan q
