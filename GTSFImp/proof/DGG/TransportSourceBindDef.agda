{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceBindDef where

-- File Charter:
--   * Defines ordinary and alignment-closing source allocation through term
--     and type scope.
--   * States the two remaining commutation lemmas needed by source-bind
--     transport through source rebasing.
--   * Each interface exposes the exact CTI constructor fields and conclusion;
--     none classifies derivations or packages a result family.
--   * The interfaces isolate only the genuinely separate induction through
--     source rebasing.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types using
  (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; `∀; ⇑ᵗ; renameᵗ;
   renameᵗ-comp; renameᵗ-cong)
open import Imprecision using (VarImp; X⊑X; _⊢_⊑_)
open import Consistency using
  (_↪ᵗ_; toRenameᵗ; wk↪ᵗ; keep)
open import TyStore using (TyStore; lookupStore; store-bind)
import TermCtx as TC
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using
  (Ctx; Term; Value; ⟨_,_,_⟩; _⊢_⦂_; renameᵗᵐ;
   ƛ_; Λ_; _↑_; _↓_)

open import proof.DGG.World
open import proof.DGG.SourceRebase
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-wk-bind; StoreRename-keep;
   toRename-wk-eq; toRename-id-eq; renameCtx-wk-eq;
   renameCtx-keep-shift)


data SourceBindScope : ∀
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
  → Set where

  source-scope-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
    → SourceBindScope wk↪ᵗ γ
        (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)

  source-scope-root-aligned : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴿ : TyVar Δᴿ}
    → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
    → (update : PivotUpdateᵗ
        (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Fin.zero
        (toRenameⁱ
          (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)) Xᴿ))
    → (boundary : AlignmentBoundaryᶜ
        (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) Fin.zero Xᴿ update)
    → (represented :
        (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ C eqᴸ ⟩
          lookupStore Σᴿ Xᴿ)
    → SourceBindScope wk↪ᵗ γ
        ((γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ▻ᶜ
          rebase-source-changeᶜ Fin.zero Xᴿ update
            (alignment-onlyᶜ boundary) represented)

  source-scope-term : ∀
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
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → (plan : SourceBindScope ρ γ γ⁺)
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : renameᵗ (toRenameᵗ ρ) A ⊑ᵀ⟨ γ⁺ ⟩ B)
    → SourceBindScope ρ
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)

  source-scope-both : ∀
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
    → SourceBindScope ρ γ γ⁺
    → SourceBindScope (keep ρ)
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γ⁺)

  source-scope-left : ∀
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
    → SourceBindScope ρ γ γ⁺
    → SourceBindScope (keep ρ) (liftLeftᶜ γ) (liftLeftᶜ γ⁺)


source-scope-center : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → SourceBindScope ρ γ γ⁺
  → centerᶜ γ ↪ᵗ centerᶜ γ⁺
source-scope-center (source-scope-root eqᴸ) = wk↪ᵗ
source-scope-center
    (source-scope-root-aligned
      eqᴸ update boundary represented) = wk↪ᵗ
source-scope-center (source-scope-term plan p p⁺) =
  source-scope-center plan
source-scope-center (source-scope-both plan) =
  keep (source-scope-center plan)
source-scope-center (source-scope-left plan) =
  keep (source-scope-center plan)


source-scope-left-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → ∀ X
  → toRenameᵗ (source-scope-center plan)
      (toRenameⁱ (ηᴸᶜ γ) X)
    ≡ toRenameⁱ (ηᴸᶜ γ⁺) (toRenameᵗ ρ X)
source-scope-left-commutes {γ = γ}
    (source-scope-root eqᴸ) X =
  trans (toRename-wk-eq (toRenameⁱ (ηᴸᶜ γ) X))
    (sym (cong (toRenameⁱ (keepⁱ (ηᴸᶜ γ)))
      (toRename-wk-eq X)))
source-scope-left-commutes {γ = γ}
    (source-scope-root-aligned
      eqᴸ update boundary represented) X =
  trans (toRename-wk-eq (toRenameⁱ (ηᴸᶜ γ) X))
    (trans
      (sym (cong (toRenameⁱ (keepⁱ (ηᴸᶜ γ)))
        (toRename-wk-eq X)))
      (sym (off-pivot-fixedᵗ update (toRenameᵗ wk↪ᵗ X) (λ ()))))
source-scope-left-commutes
    (source-scope-term plan p p⁺) X =
  source-scope-left-commutes plan X
source-scope-left-commutes (source-scope-both plan) Fin.zero = refl
source-scope-left-commutes
    (source-scope-both plan) (Fin.suc X) =
  cong Fin.suc (source-scope-left-commutes plan X)
source-scope-left-commutes (source-scope-left plan) Fin.zero = refl
source-scope-left-commutes
    (source-scope-left plan) (Fin.suc X) =
  cong Fin.suc (source-scope-left-commutes plan X)


source-scope-right-commutes : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → ∀ Y
  → toRenameᵗ (source-scope-center plan)
      (toRenameⁱ (ηᴿᶜ γ) Y)
    ≡ toRenameⁱ (ηᴿᶜ γ⁺) Y
source-scope-right-commutes {γ = γ}
    (source-scope-root eqᴸ) Y =
  toRename-wk-eq (toRenameⁱ (ηᴿᶜ γ) Y)
source-scope-right-commutes {γ = γ}
    (source-scope-root-aligned
      eqᴸ update boundary represented) Y =
  toRename-wk-eq (toRenameⁱ (ηᴿᶜ γ) Y)
source-scope-right-commutes
    (source-scope-term plan p p⁺) Y =
  source-scope-right-commutes plan Y
source-scope-right-commutes (source-scope-both plan) Fin.zero = refl
source-scope-right-commutes
    (source-scope-both plan) (Fin.suc Y) =
  cong Fin.suc (source-scope-right-commutes plan Y)
source-scope-right-commutes (source-scope-left plan) Y =
  cong Fin.suc (source-scope-right-commutes plan Y)


source-scope-mark : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → ∀ Z
  → marksᶜ γ⁺
      (toRenameᵗ (source-scope-center plan) Z)
    ≡ marksᶜ γ Z
source-scope-mark {γ = γ} (source-scope-root eqᴸ) Z =
  cong (marksᶜ γ) (toRename-id-eq Z)
source-scope-mark {γ = γ}
    (source-scope-root-aligned
      eqᴸ update boundary represented) Z =
  cong (marksᶜ γ) (toRename-id-eq Z)
source-scope-mark (source-scope-term plan p p⁺) Z =
  source-scope-mark plan Z
source-scope-mark (source-scope-both plan) Fin.zero = refl
source-scope-mark (source-scope-both plan) (Fin.suc Z) =
  source-scope-mark plan Z
source-scope-mark (source-scope-left plan) Fin.zero = refl
source-scope-mark (source-scope-left plan) (Fin.suc Z) =
  source-scope-mark plan Z


source-scope-context : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → SourceBindScope ρ γ γ⁺
  → Γᴸ⁺ ≡ TC.renameCtx (toRenameᵗ ρ) Γᴸ
source-scope-context (source-scope-root eqᴸ) =
  trans eqᴸ (sym (renameCtx-wk-eq _))
source-scope-context
    (source-scope-root-aligned
      eqᴸ update boundary represented) =
  trans eqᴸ (sym (renameCtx-wk-eq _))
source-scope-context (source-scope-term plan p p⁺) =
  cong₂ _∷_ refl (source-scope-context plan)
source-scope-context (source-scope-both {Γᴸ = Γᴸ} plan) =
  trans (cong ⇑ᶜ (source-scope-context plan))
    (sym (renameCtx-keep-shift _ Γᴸ))
source-scope-context (source-scope-left {Γᴸ = Γᴸ} plan) =
  trans (cong ⇑ᶜ (source-scope-context plan))
    (sym (renameCtx-keep-shift _ Γᴸ))


source-scope-store : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → SourceBindScope ρ γ γ⁺
  → StoreRename (toRenameᵗ ρ) Σᴸ Σᴸ⁺
source-scope-store (source-scope-root eqᴸ) = StoreRename-wk-bind
source-scope-store
    (source-scope-root-aligned
      eqᴸ update boundary represented) = StoreRename-wk-bind
source-scope-store (source-scope-term plan p p⁺) =
  source-scope-store plan
source-scope-store (source-scope-both plan) =
  StoreRename-keep (source-scope-store plan)
source-scope-store (source-scope-left plan) =
  StoreRename-keep (source-scope-store plan)


source-scope-source-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameᵗ (source-scope-center plan))
      (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A)
    ≡ renameᵗ (toRenameⁱ (ηᴸᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρ) A)
source-scope-source-type {ρ = ρ} {γ = γ} {γ⁺ = γ⁺} plan A =
  trans
    (renameᵗ-comp (toRenameⁱ (ηᴸᶜ γ))
      (toRenameᵗ (source-scope-center plan)) A)
    (trans
      (renameᵗ-cong A (source-scope-left-commutes plan))
      (sym (renameᵗ-comp (toRenameᵗ ρ)
        (toRenameⁱ (ηᴸᶜ γ⁺)) A)))


source-scope-target-type : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (source-scope-center plan))
      (renameᵗ (toRenameⁱ (ηᴿᶜ γ)) B)
    ≡ renameᵗ (toRenameⁱ (ηᴿᶜ γ⁺)) B
source-scope-target-type {γ = γ} plan B =
  trans
    (renameᵗ-comp (toRenameⁱ (ηᴿᶜ γ))
      (toRenameᵗ (source-scope-center plan)) B)
    (renameᵗ-cong B (source-scope-right-commutes plan))


source-scope-⊑ᵀ-at : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → A ⊑ᵀ⟨ γ ⟩ B
  → renameᵗ (toRenameᵗ ρ) A ⊑ᵀ⟨ γ⁺ ⟩ B
source-scope-⊑ᵀ-at {ρ = ρ} γ γ⁺ {A = A} {B = B} plan p =
  subst (λ L → marksᶜ γ⁺ ⊢ L ⊑
      renameᵗ (toRenameⁱ (ηᴿᶜ γ⁺)) B)
    (source-scope-source-type plan A)
    (subst (λ R → marksᶜ γ⁺ ⊢
        renameᵗ (toRenameᵗ (source-scope-center plan))
          (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A) ⊑ R)
      (source-scope-target-type plan B)
      (rename-⊑
        (toRenameᵗ (source-scope-center plan))
        (toRenameᵗ-injective (source-scope-center plan))
        (λ Z mark → trans (source-scope-mark plan Z) mark)
        p))


source-scope-⊑ᵀ : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → A ⊑ᵀ⟨ γ ⟩ B
  → renameᵗ (toRenameᵗ ρ) A ⊑ᵀ⟨ γ⁺ ⟩ B
source-scope-⊑ᵀ {γ = γ} {γ⁺ = γ⁺} plan p =
  source-scope-⊑ᵀ-at γ γ⁺ plan p


TransportSourceBindScopeᵀ : Set
TransportSourceBindScopeᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (plan : SourceBindScope ρ γ γ⁺)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ⁺ ⊢² renameᵗᵐ ρ M ⊑ M′ ∶ source-scope-⊑ᵀ plan p


TransportSourceBindTargetRevealRebaseᵀ : Set
TransportSourceBindTargetRevealRebaseᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → (plan : SourceBindScope ρ γ γ⁺)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → γ⁺ ⊢² renameᵗᵐ ρ M ⊑ M′ ↑ c′ ∶ source-scope-⊑ᵀ plan q


TransportSourceBindTargetConcealRebaseᵀ : Set
TransportSourceBindTargetConcealRebaseᵀ = ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴸ⁺ : TyStore Δᴸ⁺}
    {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴸ⁺ : TermCtx Δᴸ⁺}
    {Γᴿ : TermCtx Δᴿ} {ρ : Δᴸ ↪ᵗ Δᴸ⁺}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↓ Δᴿ B B′}
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → {γ⁺ : ⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindScope ρ γ γ⁺)
  → γ⁺ ⊢² renameᵗᵐ ρ M ⊑ M′ ↓ c′ ∶ source-scope-⊑ᵀ plan q
