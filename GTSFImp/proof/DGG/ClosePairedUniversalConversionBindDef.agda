{-# OPTIONS --safe #-}

module proof.DGG.ClosePairedUniversalConversionBindDef where

-- File Charter:
--   * States direct CTI compatibility for paired universal reveal and conceal
--     conversions commuting through a runtime paired bind.
--   * Returns only the post-bind type relation and CTI evidence between the
--     exact beta reducts.
--   * Contains no simulation result package, classifier, or compatibility
--     proof.

open import Data.Fin using (zero)
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyVar; `∀; _[_]ᵗ; ⇑ᵗ; ＇_)
open import TyStore using (TyStore)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_; `∀↑_; `∀↓_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⦂∀_[_]; _↑_; _↓_; ⇑ᵗᵐ)
open import Reduction using (bind; applyBody)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.World


ClosePairedUniversalRevealBindᵀ : Set
ClosePairedUniversalRevealBindᵀ = ∀ {Δᴸ Δᴿ : Nat.ℕ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {D C : Ty (Nat.suc Δᴸ)} {D′ C′ : Ty (Nat.suc Δᴿ)}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
    {c : Conv↑ (Nat.suc Δᴸ) D C}
    {c′ : Conv↑ (Nat.suc Δᴿ) D′ C′}
    {p : (`∀ D) ⊑ᵀ⟨ γ ⟩ (`∀ D′)}
  → (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] (`∀↑ c))
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] (`∀↑ c′))
  → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
  → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
  → γ ⊢² V ⊑ V′ ∶ p
  → (`∀ C) ⊑ᵀ⟨ γ ⟩ (`∀ C′)
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Value V′
  → Σ[ s ∈ ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ bindBothᶜ γ q ⟩
        ⇑ᵗ (C′ [ A′ ]ᵗ) ]
      bindBothᶜ γ q ⊢²
        ((⇑ᵗᵐ V ⦂∀ applyBody (bind A) D [ ＇ zero ]) ↑ c)
          ↑ 〖 zero , ⇑ᵗ A ↑ C 〗
        ⊑
        ((⇑ᵗᵐ V′ ⦂∀ applyBody (bind A′) D′ [ ＇ zero ]) ↑ c′)
          ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗
        ∶ s


ClosePairedUniversalConcealBindᵀ : Set
ClosePairedUniversalConcealBindᵀ = ∀ {Δᴸ Δᴿ : Nat.ℕ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {D C : Ty (Nat.suc Δᴸ)} {D′ C′ : Ty (Nat.suc Δᴿ)}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
    {c : Conv↓ (Nat.suc Δᴸ) D C}
    {c′ : Conv↓ (Nat.suc Δᴿ) D′ C′}
    {p : (`∀ D) ⊑ᵀ⟨ γ ⟩ (`∀ D′)}
  → (c⊢ : Σᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] (`∀↓ c))
  → (c′⊢ : Σᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] (`∀↓ c′))
  → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
  → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
  → γ ⊢² V ⊑ V′ ∶ p
  → (`∀ C) ⊑ᵀ⟨ γ ⟩ (`∀ C′)
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Value V′
  → Σ[ s ∈ ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ bindBothᶜ γ q ⟩
        ⇑ᵗ (C′ [ A′ ]ᵗ) ]
      bindBothᶜ γ q ⊢²
        (⇑ᵗᵐ V ⦂∀ applyBody (bind A) D [ ＇ zero ] ↓ c)
          ↑ 〖 zero , ⇑ᵗ A ↑ C 〗
        ⊑
        (⇑ᵗᵐ V′ ⦂∀ applyBody (bind A′) D′ [ ＇ zero ] ↓ c′)
          ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗
        ∶ s
