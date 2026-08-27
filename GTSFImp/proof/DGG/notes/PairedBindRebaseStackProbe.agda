{-# OPTIONS --safe #-}

module proof.DGG.notes.PairedBindRebaseStackProbe where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types using
  (Ty; TyVar; ★; ＇_; renameᵗ; renameᵗ-comp; renameᵗ-cong)
open import Imprecision using (X⊑X; ★⊑★; X⊑★; _⊢_⊑_)
open import Consistency using
  (_↪ᵗ_; empty; toRenameᵗ; wk↪ᵗ; keep; skip)
open import TyStore using (TyStore; lookupStore)
open import TermCtx using (TermCtx)
open import CastTerms using (⟨_,_,_⟩; Δᵉ)
open import proof.DGG.World
open import proof.DGG.SourceRebase
open import proof.DGG.TransportPairedBindDef using
  (PairedBindScope; paired-scope-root; paired-scope-left;
   paired-scope-center; paired-scope-left-commutes;
   paired-scope-right-commutes; paired-scope-mark; paired-scope-⊑ᵀ)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)


data PairedBindStack : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
  → (ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺)
  → (ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩)
  → Set where

  paired-stack-root : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → sourceRebaseCountᶜ γ ≡ 0
    → PairedBindScope ρᴸ ρᴿ γ γ⁺
    → PairedBindStack ρᴸ ρᴿ γ γ⁺

  paired-stack-rebase : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Xᴸ⁺ : TyVar Δᴸ⁺} {Xᴿ⁺ : TyVar Δᴿ⁺}
      {ok : CanRebaseSourceᵗ
        (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ)}
      {represented : (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ}
      {ok⁺ : CanRebaseSourceᵗ
        (ηᴸᶜ γ⁺) Xᴸ⁺ (toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ⁺)}
      {represented⁺ : (＇ Xᴸ⁺) ⊑ᵀ⟨ γ⁺ ⟩ lookupStore Σᴿ⁺ Xᴿ⁺}
    → PairedBindStack ρᴸ ρᴿ γ γ⁺
    → toRenameᵗ ρᴸ Xᴸ ≡ Xᴸ⁺
    → toRenameᵗ ρᴿ Xᴿ ≡ Xᴿ⁺
    → PairedBindStack ρᴸ ρᴿ
        (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented)
        (γ⁺ ▻ᶜ rebase-source-changeᶜ
          Xᴸ⁺ Xᴿ⁺ ok⁺ represented⁺)

  paired-stack-term : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → PairedBindStack ρᴸ ρᴿ γ γ⁺
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : renameᵗ (toRenameᵗ ρᴸ) A ⊑ᵀ⟨ γ⁺ ⟩
        renameᵗ (toRenameᵗ ρᴿ) B)
    → PairedBindStack ρᴸ ρᴿ
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)

  paired-stack-both : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → PairedBindStack ρᴸ ρᴿ γ γ⁺
    → PairedBindStack (keep ρᴸ) (keep ρᴿ)
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γ⁺)

  paired-stack-left : ∀
      {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → PairedBindStack ρᴸ ρᴿ γ γ⁺
    → PairedBindStack (keep ρᴸ) ρᴿ
        (liftLeftᶜ γ) (liftLeftᶜ γ⁺)


paired-stack-center : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → PairedBindStack ρᴸ ρᴿ γ γ⁺
  → centerᶜ γ ↪ᵗ centerᶜ γ⁺
paired-stack-center (paired-stack-root no-rebase plan) =
  paired-scope-center plan
paired-stack-center (paired-stack-rebase stack eqᴸ eqᴿ) =
  paired-stack-center stack
paired-stack-center (paired-stack-term stack p p⁺) =
  paired-stack-center stack
paired-stack-center (paired-stack-both stack) =
  keep (paired-stack-center stack)
paired-stack-center (paired-stack-left stack) =
  keep (paired-stack-center stack)


paired-stack-right-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → ∀ Y
  → toRenameᵗ (paired-stack-center stack)
      (toRenameᵗ (ηᴿᶜ γ) Y)
    ≡ toRenameᵗ (ηᴿᶜ γ⁺) (toRenameᵗ ρᴿ Y)
paired-stack-right-commutes
    (paired-stack-root no-rebase plan) Y =
  paired-scope-right-commutes plan Y
paired-stack-right-commutes
    (paired-stack-rebase stack eqᴸ eqᴿ) Y =
  paired-stack-right-commutes stack Y
paired-stack-right-commutes (paired-stack-term stack p p⁺) Y =
  paired-stack-right-commutes stack Y
paired-stack-right-commutes (paired-stack-both stack) Fin.zero = refl
paired-stack-right-commutes (paired-stack-both stack) (Fin.suc Y) =
  cong Fin.suc (paired-stack-right-commutes stack Y)
paired-stack-right-commutes (paired-stack-left stack) Y =
  cong Fin.suc (paired-stack-right-commutes stack Y)


paired-stack-left-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → ∀ X
  → toRenameᵗ (paired-stack-center stack)
      (toRenameᵗ (ηᴸᶜ γ) X)
    ≡ toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρᴸ X)
paired-stack-left-commutes
    (paired-stack-root no-rebase plan) X =
  paired-scope-left-commutes plan X
paired-stack-left-commutes {ρᴸ = ρᴸ}
    (paired-stack-rebase {Xᴸ = X} {Xᴿ = Y}
      {ok = ok} {ok⁺ = ok⁺} stack eqᴸ eqᴿ) Z
    with Z Fin.≟ X
paired-stack-left-commutes {ρᴸ = ρᴸ} {γ⁺ = γ⁺}
    (paired-stack-rebase {Xᴸ = X} {Xᴿ = Y}
      {ok = ok} {ok⁺ = ok⁺} stack eqᴸ eqᴿ) Z | yes same =
  trans
    (cong (toRenameᵗ (paired-stack-center stack))
      (trans
        (cong (toRenameᵗ (rebaseSourceEmbeddingᵗ ok)) same)
        (rebaseSource-alignedᵗ ok)))
    (trans (paired-stack-right-commutes stack Y)
      (sym (trans
        (cong (toRenameᵗ (rebaseSourceEmbeddingᵗ ok⁺))
          (trans (cong (toRenameᵗ ρᴸ) same) eqᴸ))
        (trans (rebaseSource-alignedᵗ ok⁺)
          (cong (toRenameᵗ (ηᴿᶜ γ⁺)) (sym eqᴿ))))))
paired-stack-left-commutes {ρᴸ = ρᴸ}
    (paired-stack-rebase {Xᴸ = X}
      {ok = ok} {ok⁺ = ok⁺} stack eqᴸ eqᴿ) Z | no Z≠X =
  trans
    (cong (toRenameᵗ (paired-stack-center stack))
      (rebaseSource-offᵗ ok Z Z≠X))
    (trans (paired-stack-left-commutes stack Z)
      (sym (rebaseSource-offᵗ ok⁺ (toRenameᵗ ρᴸ Z)
        image-apart)))
  where
  image-apart : toRenameᵗ ρᴸ Z ≢ _
  image-apart same = Z≠X
    (toRenameᵗ-injective ρᴸ (trans same (sym eqᴸ)))
paired-stack-left-commutes (paired-stack-term stack p p⁺) X =
  paired-stack-left-commutes stack X
paired-stack-left-commutes (paired-stack-both stack) Fin.zero = refl
paired-stack-left-commutes (paired-stack-both stack) (Fin.suc X) =
  cong Fin.suc (paired-stack-left-commutes stack X)
paired-stack-left-commutes (paired-stack-left stack) Fin.zero = refl
paired-stack-left-commutes (paired-stack-left stack) (Fin.suc X) =
  cong Fin.suc (paired-stack-left-commutes stack X)


paired-stack-mark : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → ∀ Z
  → marksᶜ γ⁺ (toRenameᵗ (paired-stack-center stack) Z)
    ≡ marksᶜ γ Z
paired-stack-mark (paired-stack-root no-rebase plan) Z =
  paired-scope-mark plan Z
paired-stack-mark (paired-stack-rebase stack eqᴸ eqᴿ) Z =
  paired-stack-mark stack Z
paired-stack-mark (paired-stack-term stack p p⁺) Z =
  paired-stack-mark stack Z
paired-stack-mark (paired-stack-both stack) Fin.zero = refl
paired-stack-mark (paired-stack-both stack) (Fin.suc Z) =
  paired-stack-mark stack Z
paired-stack-mark (paired-stack-left stack) Fin.zero = refl
paired-stack-mark (paired-stack-left stack) (Fin.suc Z) =
  paired-stack-mark stack Z


paired-stack-source-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameᵗ (paired-stack-center stack))
      (renameᵗ (toRenameᵗ (ηᴸᶜ γ)) A)
    ≡ renameᵗ (toRenameᵗ (ηᴸᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴸ) A)
paired-stack-source-type {ρᴸ = ρᴸ} {γ = γ} {γ⁺ = γ⁺} stack A =
  trans
    (renameᵗ-comp (toRenameᵗ (ηᴸᶜ γ))
      (toRenameᵗ (paired-stack-center stack)) A)
    (trans
      (renameᵗ-cong A (paired-stack-left-commutes stack))
      (sym (renameᵗ-comp (toRenameᵗ ρᴸ)
        (toRenameᵗ (ηᴸᶜ γ⁺)) A)))


paired-stack-target-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (paired-stack-center stack))
      (renameᵗ (toRenameᵗ (ηᴿᶜ γ)) B)
    ≡ renameᵗ (toRenameᵗ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴿ) B)
paired-stack-target-type {ρᴿ = ρᴿ} {γ = γ} {γ⁺ = γ⁺} stack B =
  trans
    (renameᵗ-comp (toRenameᵗ (ηᴿᶜ γ))
      (toRenameᵗ (paired-stack-center stack)) B)
    (trans
      (renameᵗ-cong B (paired-stack-right-commutes stack))
      (sym (renameᵗ-comp (toRenameᵗ ρᴿ)
        (toRenameᵗ (ηᴿᶜ γ⁺)) B)))


paired-stack-⊑ᵀ : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (stack : PairedBindStack ρᴸ ρᴿ γ γ⁺)
  → A ⊑ᵀ⟨ γ ⟩ B
  → renameᵗ (toRenameᵗ ρᴸ) A ⊑ᵀ⟨ γ⁺ ⟩
      renameᵗ (toRenameᵗ ρᴿ) B
paired-stack-⊑ᵀ {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ = γ} {γ⁺ = γ⁺}
    {A = A} {B = B} stack p =
  subst (λ L → marksᶜ γ⁺ ⊢ L ⊑
      renameᵗ (toRenameᵗ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρᴿ) B))
    (paired-stack-source-type stack A)
    (subst (λ R → marksᶜ γ⁺ ⊢
        renameᵗ (toRenameᵗ (paired-stack-center stack))
          (renameᵗ (toRenameᵗ (ηᴸᶜ γ)) A) ⊑ R)
      (paired-stack-target-type stack B)
      (rename-⊑
        (toRenameᵗ (paired-stack-center stack))
        (toRenameᵗ-injective (paired-stack-center stack))
        (λ Z mark → trans (paired-stack-mark stack Z) mark)
        p))


data ScopeSourceRebaseᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → Γᴸ ⊑ᶜ Γᴿ
    → TyVar (Δᵉ Γᴸ)
    → TyVar (Δᵉ Γᴿ)
    → Set where

  scope-source-rebase : ∀ {Γᴸ Γᴿ}
      {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ

  scope-source-rebase-term : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (pᵖ : A ⊑ᵀ⟨ γᵖ ⟩ B)
    → ScopeSourceRebaseᶜ
        (bind-termᶜ γ p) (bind-termᶜ γᵖ pᵖ) Xᴸ Xᴿ

  scope-source-rebase-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → ScopeSourceRebaseᶜ
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γᵖ)
        (Fin.suc Xᴸ) (Fin.suc Xᴿ)

  scope-source-rebase-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → ScopeSourceRebaseᶜ
        (liftLeftᶜ γ) (liftLeftᶜ γᵖ) (Fin.suc Xᴸ) Xᴿ


scope-source-rebase-nonzero : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → sourceRebaseCountᶜ γᵖ ≢ 0
scope-source-rebase-nonzero (scope-source-rebase rebase) =
  source-rebase-count≢zero rebase
scope-source-rebase-nonzero
    (scope-source-rebase-term rebase p pᵖ) =
  scope-source-rebase-nonzero rebase
scope-source-rebase-nonzero (scope-source-rebase-both rebase) =
  scope-source-rebase-nonzero rebase
scope-source-rebase-nonzero (scope-source-rebase-left rebase) =
  scope-source-rebase-nonzero rebase


paired-stack-pop : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → PairedBindStack ρᴸ ρᴿ γᵖ γᵖ⁺
  → ScopeSourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → Σ[ γ⁺ ∈ (⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩) ]
    Σ[ Xᴸ⁺ ∈ TyVar Δᴸ⁺ ]
    Σ[ Xᴿ⁺ ∈ TyVar Δᴿ⁺ ]
      (toRenameᵗ ρᴸ Xᴸ ≡ Xᴸ⁺)
      × (toRenameᵗ ρᴿ Xᴿ ≡ Xᴿ⁺)
      × PairedBindStack ρᴸ ρᴿ γ γ⁺
      × ScopeSourceRebaseᶜ γ⁺ γᵖ⁺ Xᴸ⁺ Xᴿ⁺
paired-stack-pop (paired-stack-root no-rebase plan) rebase =
  ⊥-elim (scope-source-rebase-nonzero rebase no-rebase)
paired-stack-pop
    (paired-stack-rebase {ok⁺ = ok⁺} {represented⁺ = represented⁺}
      stack eqᴸ eqᴿ)
    (scope-source-rebase (source-rebase-now ok represented)) =
  _ , _ , _ , eqᴸ , eqᴿ , stack ,
    scope-source-rebase (source-rebase-now ok⁺ represented⁺)
paired-stack-pop
    (paired-stack-term stack pᵖ pᵖ⁺)
    (scope-source-rebase-term rebase p pᵖ)
    with paired-stack-pop stack rebase
paired-stack-pop
    (paired-stack-term stack pᵖ pᵖ⁺)
    (scope-source-rebase-term rebase p pᵖ)
    | γ⁺ , Xᴸ⁺ , Xᴿ⁺ , eqᴸ , eqᴿ , stack⁰ , rebase⁺ =
  bind-termᶜ γ⁺ p⁺ , Xᴸ⁺ , Xᴿ⁺ , eqᴸ , eqᴿ ,
    paired-stack-term stack⁰ p p⁺ ,
    scope-source-rebase-term rebase⁺ p⁺ pᵖ⁺
  where
  p⁺ = paired-stack-⊑ᵀ stack⁰ p

paired-stack-pop
    (paired-stack-both stack)
    (scope-source-rebase-both rebase)
    with paired-stack-pop stack rebase
paired-stack-pop
    (paired-stack-both stack)
    (scope-source-rebase-both rebase)
    | γ⁺ , Xᴸ⁺ , Xᴿ⁺ , eqᴸ , eqᴿ , stack⁰ , rebase⁺ =
  liftBothᶜ X⊑X γ⁺ , Fin.suc Xᴸ⁺ , Fin.suc Xᴿ⁺ ,
    cong Fin.suc eqᴸ , cong Fin.suc eqᴿ ,
    paired-stack-both stack⁰ , scope-source-rebase-both rebase⁺

paired-stack-pop
    (paired-stack-left stack)
    (scope-source-rebase-left rebase)
    with paired-stack-pop stack rebase
paired-stack-pop
    (paired-stack-left stack)
    (scope-source-rebase-left rebase)
    | γ⁺ , Xᴸ⁺ , Xᴿ⁺ , eqᴸ , eqᴿ , stack⁰ , rebase⁺ =
  liftLeftᶜ γ⁺ , Fin.suc Xᴸ⁺ , Xᴿ⁺ ,
    cong Fin.suc eqᴸ , eqᴿ ,
    paired-stack-left stack⁰ , scope-source-rebase-left rebase⁺


paired-left-zero-before : CanRebaseSourceᵗ
    (keep (skip (keep (empty {Δ = 0}))))
    Fin.zero (Fin.suc Fin.zero)
paired-left-zero-before =
  can-rebase-sourceᵗ (λ ()) (insert-skipᵗ insert-hereᵗ)


paired-left-zero-after-impossible : CanRebaseSourceᵗ
    (keep (keep (skip (keep (empty {Δ = 0}))))) Fin.zero
    (Fin.suc (Fin.suc Fin.zero))
  → ⊥
paired-left-zero-after-impossible
    (can-rebase-sourceᵗ apart (insert-skipᵗ ()))


paired-left-zero-rebase-exists :
  let γ₀ = bindRightᶜ (bindBothᶜ emptyᶜ ★⊑★) ★ (inj₁ refl)
      γ = liftLeftᶜ γ₀
      represented : (＇ Fin.zero) ⊑ᵀ⟨ γ ⟩ ★
      represented = X⊑★ refl
  in SourceRebaseᶜ γ
      (γ ▻ᶜ rebase-source-changeᶜ
        Fin.zero Fin.zero paired-left-zero-before represented)
      Fin.zero Fin.zero
paired-left-zero-rebase-exists =
  source-rebase-now paired-left-zero-before (X⊑★ refl)


paired-left-zero-plan :
  let γ₀ = bindRightᶜ (bindBothᶜ emptyᶜ ★⊑★) ★ (inj₁ refl)
  in PairedBindScope (keep wk↪ᵗ) wk↪ᵗ
      (liftLeftᶜ γ₀) (liftLeftᶜ (bindBothᶜ γ₀ ★⊑★))
paired-left-zero-plan =
  paired-scope-left (paired-scope-root ★⊑★ refl refl)


paired-left-zero-plan-output-impossible :
  let γ₀ = bindRightᶜ (bindBothᶜ emptyᶜ ★⊑★) ★ (inj₁ refl)
      γ⁺ = liftLeftᶜ (bindBothᶜ γ₀ ★⊑★)
  in CanRebaseSourceᵗ (ηᴸᶜ γ⁺) Fin.zero
      (toRenameᵗ (ηᴿᶜ γ⁺) (Fin.suc Fin.zero))
    → ⊥
paired-left-zero-plan-output-impossible =
  paired-left-zero-after-impossible
