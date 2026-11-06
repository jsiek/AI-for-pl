{-# OPTIONS --safe #-}

module proof.DGG.CastTermImprecision where

-- File Charter:
--   * Defines cast-term imprecision directly over the canonical relation
--     between two complete CastTerms contexts.
--   * Uses the endpoint type stores and term contexts from the world indices;
--     there is no separate context-imprecision list or compatibility world.
--   * Treats the world as an index so reveal and conceal may move along the
--     canonical source-rebase relation.
--   * Keeps paired conversions in one world and reserves one-sided rules for
--     genuinely one-sided syntax.
--   * Keeps rules syntax directed and avoids packaged action wrappers.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision
open import TyStore using (lookupStore)
open import Primitives using
  (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms using
  (Ctx; Δᵉ; Σᵉ; Term; Value; _∋ᵗ_⦂_; _⊢_⦂_; `_; ƛ_; _·_; Λ_;
   _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)

open import proof.DGG.World
open import proof.DGG.SourceRebase
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)


------------------------------------------------------------------------
-- Typed cast-term imprecision over complete endpoint contexts
------------------------------------------------------------------------

infix 4 _⊢²_⊑_∶_

variable
  Γᴸ Γᴿ : Ctx
  γ : Γᴸ ⊑ᶜ Γᴿ

data _⊢²_⊑_∶_ {Γᴸ Γᴿ : Ctx} :
    (γ : Γᴸ ⊑ᶜ Γᴿ)
    → Term (Δᵉ Γᴸ) → Term (Δᵉ Γᴿ)
    → {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    → A ⊑ᵀ⟨ γ ⟩ B → Set where

  x⊑x² : ∀ {x A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
    → Γᴸ ∋ᵗ x ⦂ A
    → Γᴿ ∋ᵗ x ⦂ B
      ------------------------
    → γ ⊢² ` x ⊑ ` x ∶ p

  ƛ⊑ƛ² : ∀ {M M′ A A′ B B′}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    → bind-termᶜ γ pA ⊢² M ⊑ M′ ∶ pB
      -----------------------------------
    → γ ⊢² ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

  ·⊑·² : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → γ ⊢² M ⊑ M′ ∶ pA
      -----------------------------
    → γ ⊢² L · M ⊑ L′ · M′ ∶ pB

  Λ⊑Λ² : ∀ {V V′ A B}
      {p : A ⊑ᵀ⟨ liftBothᶜ X⊑X γ ⟩ B}
    → Value V
    → Value V′
    → liftBothᶜ X⊑X γ ⊢² V ⊑ V′ ∶ p
    → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ (`∀ B))
      ---------------------------------
    → γ ⊢² Λ V ⊑ Λ V′ ∶ q

  Λ⊑² : ∀ {V M A B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → {p : A ⊑ᵀ⟨ γ ▻ᶜ lift-left-changeᶜ refl ⟩ B}
    → Value V
    → Γᴿ ⊢ M ⦂ B
    → (γ ▻ᶜ lift-left-changeᶜ refl) ⊢² V ⊑ M ∶ p
    → (q : (`∀ A) ⊑ᵀ⟨ γ ⟩ B)
      -----------------------
    → γ ⊢² Λ V ⊑ M ∶ q

  •⊑•² : ∀ {M M′ C C′ A A′}
    → (p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ (`∀ C′))
    → γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵀ⟨ γ ⟩ A′)
    → (r : (C [ A ]ᵗ) ⊑ᵀ⟨ γ ⟩ (C′ [ A′ ]ᵗ))
      -----------------------------------------
    → γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ r

  •⊑² : ∀ {M M′ C A B}
    → (p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ B)
    → γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵀ⟨ γ ⟩ ★)
    → (r : (C [ A ]ᵗ) ⊑ᵀ⟨ γ ⟩ B)
      ------------------------------
    → γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ∶ r

  κ⊑κ² : ∀ (κ : Const)
    → (p : constTy κ ⊑ᵀ⟨ γ ⟩ constTy κ)
      ----------------------------------
    → γ ⊢² $ κ ⊑ $ κ ∶ p

  cast⊑cast² : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵀ⟨ γ ⟩ C′}
      {ν : Env∼ (Δᵉ Γᴸ)} {ν′ : Env∼ (Δᵉ Γᴿ)}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ A′)
      -----------------------------
    → γ ⊢² M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑cast² : ∀ {M M′ A B B′}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {ν : Env∼ (Δᵉ Γᴿ)}
    → (c′ : ν ⊢ B ∼ B′)
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑reveal-identity : ∀ {M M′ A B B′ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c′⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-identity : ∀ {M M′ A B B′ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c′⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q

  cast⊑² : ∀ {M M′ A A′ B}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {ν : Env∼ (Δᵉ Γᴸ)}
    → (c : ν ⊢ A ∼ A′)
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ q

  reveal⊑-identity : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  reveal⊑-only² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  conceal⊑-identity : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  conceal⊑-only² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀ {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
    → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ γ ⟩ A′}
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀
      {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ A′}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
    → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

  ⊑reveal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q

  blame⊑² : ∀ {M′ A B}
    → Γᴿ ⊢ M′ ⦂ B
    → (p : A ⊑ᵀ⟨ γ ⟩ B)
      --------------------
    → γ ⊢² blame ⊑ M′ ∶ p

  ⊕⊑⊕² : (op : Prim)
    → ∀ {L L′ M M′}
      {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
    → γ ⊢² L ⊑ L′ ∶ p
    → γ ⊢² M ⊑ M′ ∶ q
    → (r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
      ---------------------------------------------
    → γ ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ r
