{-# OPTIONS --safe #-}

module proof.DGG.CastTermImprecision where

-- File Charter:
--   * Defines cast-term imprecision directly over the canonical relation
--     between two complete CastTerms contexts.
--   * Uses the endpoint type stores and term contexts from the world indices;
--     there is no separate context-imprecision list or compatibility world.
--   * Uses structural plans for source-only universal binders and source
--     rebasing.  These plans rebuild only constructor-form worlds.
--   * Mechanically carries the current conversion-generator and occupancy
--     premises into the canonical world.  The reveal and conceal rules remain
--     subject to a separate semantic review against reduction and examples.
--   * Keeps rules syntax directed and avoids packaged action wrappers.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision
open import Primitives using
  (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms using
  (Ctx; Δᵉ; Σᵉ; Term; Value; _∋ᵗ_⦂_; _⊢_⦂_; `_; ƛ_; _·_; Λ_;
   _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)

open import proof.DGG.World
open import proof.DGG.SourceRebasePlan using
  (SourceRebasePlan; rebaseSource)
open import proof.DGG.SourceFreshBehindPlan using
  (SourceFreshBehindPlan; insertSourceFreshBehind)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)


------------------------------------------------------------------------
-- Typed cast-term imprecision over complete endpoint contexts
------------------------------------------------------------------------

infix 4 _⊢²_⊑_∶_

data _⊢²_⊑_∶_ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ) :
    Term (Δᵉ Γᴸ) → Term (Δᵉ Γᴿ)
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
    → (plan : SourceFreshBehindPlan γ)
    → {p : A ⊑ᵀ⟨ insertSourceFreshBehind plan ⟩ B}
    → Value V
    → Γᴿ ⊢ M ⦂ B
    → insertSourceFreshBehind plan ⊢² V ⊑ M ∶ p
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

  ⊑reveal² : ∀ {M M′ A B B′ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c′⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal² : ∀ {M M′ A B B′ Xᴿ Rᴿ}
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

  reveal⊑-neutral² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
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
    → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  reveal⊑² : ∀ {M M′ A A′ B Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → toRenameᵗ (ηᴸᶜ γ) Xᴸ ≢ toRenameᵗ (ηᴿᶜ γ) Xᴿ
    → (plan : SourceRebasePlan γ Xᴸ Xᴿ)
    → Rᴸ ⊑ᵀ⟨ rebaseSource plan ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ rebaseSource plan ⟩ B}
    → rebaseSource plan ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↑ c ⊑ M′ ∶ q

  conceal⊑-neutral² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≡ generator-absent
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  conceal⊑² : ∀ {M M′ A A′ B Xᴸ Rᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {c : Conv↓ (Δᵉ Γᴸ) A A′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
        ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
    → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
      ---------------------
    → γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀ {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (plan : SourceRebasePlan γ Xᴸ Xᴿ)
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → Rᴸ ⊑ᵀ⟨ rebaseSource plan ⟩ Rᴿ
    → {p : A ⊑ᵀ⟨ rebaseSource plan ⟩ A′}
    → rebaseSource plan ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A A′ B B′ Xᴸ Xᴿ Rᴸ Rᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ A′}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (plan : SourceRebasePlan γᵖ Xᴸ Xᴿ)
    → rebaseSource plan ≡ γ
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → Rᴸ ⊑ᵀ⟨ rebaseSource plan ⟩ Rᴿ
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ γ ⟩ B′)
      ------------------------------
    → γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

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
