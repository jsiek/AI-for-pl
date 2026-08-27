{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceBindDef where

-- File Charter:
--   * States the five commutation lemmas needed by source-bind transport.
--   * Each interface exposes the exact CTI constructor fields and conclusion;
--     none classifies derivations or packages a result family.
--   * The interfaces separate genuinely different inductions through term
--     scope, type scope, and source rebasing.

import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; `∀; _⇒_)
open import Imprecision using (⇒⊑⇒; X⊑X)
open import Consistency using (toRenameᵗ)
open import TyStore using (TyStore; lookupStore)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using
  (Ctx; Term; Value; ⟨_,_,_⟩; _⊢_⦂_; ⇑ᵗᵐ; ƛ_; Λ_; _↑_; _↓_)

open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-bind-left; evolution-⊑ᵀ)
open import proof.DGG.CastTermImprecision using
  (_⊢²_⊑_∶_; ƛ⊑ƛ²; Λ⊑Λ²; Λ⊑²; ⊑reveal-rebase²;
   ⊑conceal-rebase²)


TransportSourceBindLambdaᵀ : Set
TransportSourceBindLambdaᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → bind-termᶜ γ pA ⊢² M ⊑ M′ ∶ pB
  → (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢²
      ⇑ᵗᵐ (ƛ M) ⊑ ƛ M′
      ∶ evolution-⊑ᵀ
        (evolution-bind-left {A = C} {W = γ} eqᴸ) (⇒⊑⇒ pA pB)


TransportSourceBindTypeLambdaᵀ : Set
TransportSourceBindTypeLambdaᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {V : Term (Nat.suc Δᴸ)} {V′ : Term (Nat.suc Δᴿ)}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty (Nat.suc Δᴿ)}
    {p : A ⊑ᵀ⟨ liftBothᶜ X⊑X γ ⟩ B}
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → Value V
  → Value V′
  → liftBothᶜ X⊑X γ ⊢² V ⊑ V′ ∶ p
  → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ (`∀ B))
  → (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢²
      ⇑ᵗᵐ (Λ V) ⊑ Λ V′
      ∶ evolution-⊑ᵀ
        (evolution-bind-left {A = C} {W = γ} eqᴸ) q


TransportSourceBindSourceLambdaᵀ : Set
TransportSourceBindSourceLambdaᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {V : Term (Nat.suc Δᴸ)} {M : Term Δᴿ}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵀ⟨ γ ▻ᶜ lift-left-changeᶜ refl ⟩ B}
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → ⟨ Δᴿ , Σᴿ , Γᴿ ⟩ ⊢ M ⦂ B
  → (γ ▻ᶜ lift-left-changeᶜ refl) ⊢² V ⊑ M ∶ p
  → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ B)
  → (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢²
      ⇑ᵗᵐ (Λ V) ⊑ M
      ∶ evolution-⊑ᵀ
        (evolution-bind-left {A = C} {W = γ} eqᴸ) q


TransportSourceBindTargetRevealRebaseᵀ : Set
TransportSourceBindTargetRevealRebaseᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c′ : Conv↑ Δᴿ B B′}
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
  → {p : A ⊑ᵀ⟨
      γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B}
  → (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented) ⊢²
      M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢²
      ⇑ᵗᵐ M ⊑ M′ ↑ c′
      ∶ evolution-⊑ᵀ
        (evolution-bind-left {A = C} {W = γ} eqᴸ) q


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
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → (ok : CanRebaseSourceᵗ
      (ηᴸᶜ γᵖ) Xᴸ (toRenameᵗ (ηᴿᶜ γᵖ) Xᴿ))
  → (represented : (＇ Xᴸ) ⊑ᵀ⟨ γᵖ ⟩ lookupStore Σᴿ Xᴿ)
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨
      γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented ⟩ B′)
  → (γᵖ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented
      ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢²
      ⇑ᵗᵐ M ⊑ M′ ↓ c′
      ∶ evolution-⊑ᵀ
        (evolution-bind-left
          {A = C}
          {W = γᵖ ▻ᶜ
            rebase-source-changeᶜ Xᴸ Xᴿ ok represented}
          eqᴸ)
        q
