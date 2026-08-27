{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceBindDef where

-- File Charter:
--   * Defines source allocation through a prefix of term binders.
--   * States the four remaining commutation lemmas needed by source-bind
--     transport through type scope and source rebasing.
--   * Each interface exposes the exact CTI constructor fields and conclusion;
--     none classifies derivations or packages a result family.
--   * The interfaces separate genuinely different inductions through term
--     scope, type scope, and source rebasing.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; `∀; ⇑ᵗ)
open import Imprecision using (X⊑X)
open import Consistency using (toRenameᵗ)
open import TyStore using (TyStore; lookupStore; store-bind)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using
  (Ctx; Term; Value; ⟨_,_,_⟩; _⊢_⦂_; ⇑ᵗᵐ; ƛ_; Λ_; _↑_; _↓_)

open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-bind-left; evolution-⊑ᵀ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)


data SourceBindThroughTerms : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → Set where

  source-bind-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
    → SourceBindThroughTerms γ
        (γ ▻ᶜ bind-left-changeᶜ C eqᴸ)

  source-bind-term : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → (plan : SourceBindThroughTerms γ γ⁺)
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
    → (p⁺ : ⇑ᵗ A ⊑ᵀ⟨ γ⁺ ⟩ B)
    → SourceBindThroughTerms
        (bind-termᶜ γ p) (bind-termᶜ γ⁺ p⁺)


source-bind-⊑ᵀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → SourceBindThroughTerms γ γ⁺
  → A ⊑ᵀ⟨ γ ⟩ B
  → ⇑ᵗ A ⊑ᵀ⟨ γ⁺ ⟩ B
source-bind-⊑ᵀ {C = C} {γ = γ} (source-bind-root eqᴸ) p =
  evolution-⊑ᵀ
    (evolution-bind-left {A = C} {W = γ} eqᴸ) p
source-bind-⊑ᵀ (source-bind-term plan p p⁺) q =
  source-bind-⊑ᵀ plan q


TransportSourceBindThroughTermsᵀ : Set
TransportSourceBindThroughTermsᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (plan : SourceBindThroughTerms γ γ⁺)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ⁺ ⊢² ⇑ᵗᵐ M ⊑ M′ ∶ source-bind-⊑ᵀ plan p


TransportSourceBindTypeLambdaᵀ : Set
TransportSourceBindTypeLambdaᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {V : Term (Nat.suc Δᴸ)} {V′ : Term (Nat.suc Δᴿ)}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty (Nat.suc Δᴿ)}
    {p : A ⊑ᵀ⟨ liftBothᶜ X⊑X γ ⟩ B}
  → (plan : SourceBindThroughTerms γ γ⁺)
  → Value V
  → Value V′
  → liftBothᶜ X⊑X γ ⊢² V ⊑ V′ ∶ p
  → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ (`∀ B))
  → γ⁺ ⊢² ⇑ᵗᵐ (Λ V) ⊑ Λ V′ ∶ source-bind-⊑ᵀ plan q


TransportSourceBindSourceLambdaᵀ : Set
TransportSourceBindSourceLambdaᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {V : Term (Nat.suc Δᴸ)} {M : Term Δᴿ}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵀ⟨ γ ▻ᶜ lift-left-changeᶜ refl ⟩ B}
  → (plan : SourceBindThroughTerms γ γ⁺)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → ⟨ Δᴿ , Σᴿ , Γᴿ ⟩ ⊢ M ⦂ B
  → (γ ▻ᶜ lift-left-changeᶜ refl) ⊢² V ⊑ M ∶ p
  → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ B)
  → γ⁺ ⊢² ⇑ᵗᵐ (Λ V) ⊑ M ∶ source-bind-⊑ᵀ plan q


TransportSourceBindTargetRevealRebaseᵀ : Set
TransportSourceBindTargetRevealRebaseᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → (plan : SourceBindThroughTerms γ γ⁺)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
  → {p : A ⊑ᵀ⟨
      γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B}
  → (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented) ⊢²
      M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → γ⁺ ⊢² ⇑ᵗᵐ M ⊑ M′ ↑ c′ ∶ source-bind-⊑ᵀ plan q


TransportSourceBindTargetConcealRebaseᵀ : Set
TransportSourceBindTargetConcealRebaseᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↓ Δᴿ B B′}
    {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γᵖ) Xᴸ (toRenameᵗ (ηᴿᶜ γᵖ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γᵖ ⟩ lookupStore Σᴿ Xᴿ)
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨
      γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B′)
  → {γ⁺ : ⟨ Nat.suc Δᴸ , store-bind Σᴸ C , Γᴸ⁺ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → (plan : SourceBindThroughTerms
      (γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented) γ⁺)
  → γ⁺ ⊢² ⇑ᵗᵐ M ⊑ M′ ↓ c′ ∶ source-bind-⊑ᵀ plan q
