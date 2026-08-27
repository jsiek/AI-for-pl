{-# OPTIONS --safe #-}

module proof.DGG.TransportTargetBindDef where

-- File Charter:
--   * Defines target allocation through term and type scope.
--   * Derives the center, context, store, and type-imprecision actions of
--     that structural scope graph.
--   * States only the two source-rebase commutations that require a separate
--     induction.
--   * Contains no compatibility world, classifier, or result wrapper.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types using
  (Ty; TyVar; ＇_; renameᵗ; renameᵗ-comp; renameᵗ-cong)
open import Imprecision using (X⊑X; _⊢_⊑_)
open import Consistency using
  (_↪ᵗ_; toRenameᵗ; wk↪ᵗ; keep)
open import TyStore using (TyStore; lookupStore; store-bind)
import TermCtx as TC
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using
  (Ctx; Term; ⟨_,_,_⟩; _⊢_⦂_; renameᵗᵐ; _↑_; _↓_)

open import proof.DGG.World
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-wk-bind; StoreRename-keep;
   toRename-wk-eq; toRename-id-eq; renameCtx-wk-eq;
   renameCtx-keep-shift)


data TargetBindScope : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
  → (ρ : Δᴿ ↪ᵗ Δᴿ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩)
  → Set where

  target-scope-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)} {C : Ty Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (fresh : RightBindFreshᶜ γ C)
    → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
    → TargetBindScope wk↪ᵗ γ
        (γ ▻ᶜ bind-right-changeᶜ C fresh eqᴿ)

  target-scope-term : ∀
      {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → (plan : TargetBindScope ρ γ γ⁺)
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : A ⊑ᵀ⟨ γ⁺ ⟩ renameᵗ (toRenameᵗ ρ) B)
    → TargetBindScope ρ
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)

  target-scope-both : ∀
      {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → TargetBindScope ρ γ γ⁺
    → TargetBindScope (keep ρ)
        (liftBothᶜ X⊑X γ) (liftBothᶜ X⊑X γ⁺)

  target-scope-left : ∀
      {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    → TargetBindScope ρ γ γ⁺
    → TargetBindScope ρ (liftLeftᶜ γ) (liftLeftᶜ γ⁺)


target-scope-center : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → TargetBindScope ρ γ γ⁺
  → centerᶜ γ ↪ᵗ centerᶜ γ⁺
target-scope-center (target-scope-root fresh eqᴿ) = wk↪ᵗ
target-scope-center (target-scope-term plan p p⁺) =
  target-scope-center plan
target-scope-center (target-scope-both plan) =
  keep (target-scope-center plan)
target-scope-center (target-scope-left plan) =
  keep (target-scope-center plan)


target-scope-left-commutes : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ γ γ⁺)
  → ∀ X
  → toRenameᵗ (target-scope-center plan)
      (toRenameᵗ (ηᴸᶜ γ) X)
    ≡ toRenameᵗ (ηᴸᶜ γ⁺) X
target-scope-left-commutes {γ = γ}
    (target-scope-root fresh eqᴿ) X =
  toRename-wk-eq (toRenameᵗ (ηᴸᶜ γ) X)
target-scope-left-commutes (target-scope-term plan p p⁺) X =
  target-scope-left-commutes plan X
target-scope-left-commutes (target-scope-both plan) Fin.zero = refl
target-scope-left-commutes (target-scope-both plan) (Fin.suc X) =
  cong Fin.suc (target-scope-left-commutes plan X)
target-scope-left-commutes (target-scope-left plan) Fin.zero = refl
target-scope-left-commutes (target-scope-left plan) (Fin.suc X) =
  cong Fin.suc (target-scope-left-commutes plan X)


target-scope-right-commutes : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ γ γ⁺)
  → ∀ Y
  → toRenameᵗ (target-scope-center plan)
      (toRenameᵗ (ηᴿᶜ γ) Y)
    ≡ toRenameᵗ (ηᴿᶜ γ⁺) (toRenameᵗ ρ Y)
target-scope-right-commutes {γ = γ}
    (target-scope-root fresh eqᴿ) Y =
  trans (toRename-wk-eq (toRenameᵗ (ηᴿᶜ γ) Y))
    (sym (cong (toRenameᵗ (keep (ηᴿᶜ γ)))
      (toRename-wk-eq Y)))
target-scope-right-commutes (target-scope-term plan p p⁺) Y =
  target-scope-right-commutes plan Y
target-scope-right-commutes (target-scope-both plan) Fin.zero = refl
target-scope-right-commutes (target-scope-both plan) (Fin.suc Y) =
  cong Fin.suc (target-scope-right-commutes plan Y)
target-scope-right-commutes (target-scope-left plan) Y =
  cong Fin.suc (target-scope-right-commutes plan Y)


target-scope-mark : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ γ γ⁺)
  → ∀ Z
  → marksᶜ γ⁺ (toRenameᵗ (target-scope-center plan) Z)
    ≡ marksᶜ γ Z
target-scope-mark {γ = γ} (target-scope-root fresh eqᴿ) Z =
  cong (marksᶜ γ) (toRename-id-eq Z)
target-scope-mark (target-scope-term plan p p⁺) Z =
  target-scope-mark plan Z
target-scope-mark (target-scope-both plan) Fin.zero = refl
target-scope-mark (target-scope-both plan) (Fin.suc Z) =
  target-scope-mark plan Z
target-scope-mark (target-scope-left plan) Fin.zero = refl
target-scope-mark (target-scope-left plan) (Fin.suc Z) =
  target-scope-mark plan Z


target-scope-context : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → TargetBindScope ρ γ γ⁺
  → Γᴿ⁺ ≡ TC.renameCtx (toRenameᵗ ρ) Γᴿ
target-scope-context (target-scope-root fresh eqᴿ) =
  trans eqᴿ (sym (renameCtx-wk-eq _))
target-scope-context (target-scope-term plan p p⁺) =
  cong₂ _∷_ refl (target-scope-context plan)
target-scope-context (target-scope-both {Γᴿ = Γᴿ} plan) =
  trans (cong ⇑ᶜ (target-scope-context plan))
    (sym (renameCtx-keep-shift _ Γᴿ))
target-scope-context (target-scope-left {Γᴿ = Γᴿ} plan) =
  target-scope-context plan


target-scope-store : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → TargetBindScope ρ γ γ⁺
  → StoreRename (toRenameᵗ ρ) Σᴿ Σᴿ⁺
target-scope-store (target-scope-root fresh eqᴿ) = StoreRename-wk-bind
target-scope-store (target-scope-term plan p p⁺) =
  target-scope-store plan
target-scope-store (target-scope-both plan) =
  StoreRename-keep (target-scope-store plan)
target-scope-store (target-scope-left plan) =
  target-scope-store plan


target-scope-source-type : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ γ γ⁺)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameᵗ (target-scope-center plan))
      (renameᵗ (toRenameᵗ (ηᴸᶜ γ)) A)
    ≡ renameᵗ (toRenameᵗ (ηᴸᶜ γ⁺)) A
target-scope-source-type {γ = γ} plan A =
  trans
    (renameᵗ-comp (toRenameᵗ (ηᴸᶜ γ))
      (toRenameᵗ (target-scope-center plan)) A)
    (renameᵗ-cong A (target-scope-left-commutes plan))


target-scope-target-type : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ γ γ⁺)
  → (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (target-scope-center plan))
      (renameᵗ (toRenameᵗ (ηᴿᶜ γ)) B)
    ≡ renameᵗ (toRenameᵗ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρ) B)
target-scope-target-type {ρ = ρ} {γ = γ} {γ⁺ = γ⁺} plan B =
  trans
    (renameᵗ-comp (toRenameᵗ (ηᴿᶜ γ))
      (toRenameᵗ (target-scope-center plan)) B)
    (trans
      (renameᵗ-cong B (target-scope-right-commutes plan))
      (sym (renameᵗ-comp (toRenameᵗ ρ)
        (toRenameᵗ (ηᴿᶜ γ⁺)) B)))


target-scope-⊑ᵀ : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → A ⊑ᵀ⟨ γ ⟩ B
  → A ⊑ᵀ⟨ γ⁺ ⟩ renameᵗ (toRenameᵗ ρ) B
target-scope-⊑ᵀ {ρ = ρ} {γ = γ} {γ⁺ = γ⁺} {A = A} {B = B}
    plan p =
  subst (λ L → marksᶜ γ⁺ ⊢ L ⊑
      renameᵗ (toRenameᵗ (ηᴿᶜ γ⁺))
        (renameᵗ (toRenameᵗ ρ) B))
    (target-scope-source-type plan A)
    (subst (λ R → marksᶜ γ⁺ ⊢
        renameᵗ (toRenameᵗ (target-scope-center plan))
          (renameᵗ (toRenameᵗ (ηᴸᶜ γ)) A) ⊑ R)
      (target-scope-target-type plan B)
      (rename-⊑
        (toRenameᵗ (target-scope-center plan))
        (toRenameᵗ-injective (target-scope-center plan))
        (λ Z mark → trans (target-scope-mark plan Z) mark)
        p))


TransportTargetBindScopeᵀ : Set
TransportTargetBindScopeᵀ = ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (plan : TargetBindScope ρ γ γ⁺)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ⁺ ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ target-scope-⊑ᵀ plan p


TransportTargetBindRevealRebaseᵀ : Set
TransportTargetBindRevealRebaseᵀ = ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ΔA : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
  → {p : ΔA ⊑ᵀ⟨
      γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B}
  → (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented) ⊢²
      M ⊑ M′ ∶ p
  → (q : ΔA ⊑ᵀ⟨ γ ⟩ B′)
  → γ⁺ ⊢² M ⊑ renameᵗᵐ ρ (M′ ↑ c′)
      ∶ target-scope-⊑ᵀ plan q


TransportTargetBindConcealRebaseᵀ : Set
TransportTargetBindConcealRebaseᵀ = ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↓ Δᴿ B B′}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γᵖ) Xᴸ (toRenameᵗ (ηᴿᶜ γᵖ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γᵖ ⟩ lookupStore Σᴿ Xᴿ)
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨
      γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B′)
  → {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
  → {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
  → (plan : TargetBindScope ρ
      (γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented) γ⁺)
  → γ⁺ ⊢² M ⊑ renameᵗᵐ ρ (M′ ↓ c′)
      ∶ target-scope-⊑ᵀ plan q
