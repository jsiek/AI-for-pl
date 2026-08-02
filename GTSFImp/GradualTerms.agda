module GradualTerms where

-- File Charter:
--   * Source-language gradual term syntax and typing for GTSFImp.
--   * Uses intrinsically scoped types and the consistency relation.
--   * Contains no casts; well-typed source terms are intended to compile to
--     the cast calculus in CastTerms.
--   * Exports type-variable renaming and weakening for gradual terms.
--   * Application and primitive-operation nodes retain source blame labels.

open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)

open import Types
open import TermCtx
open import Consistency using (_∼_)
open import Primitives
  using (Const; Prim; constTy; primArgTy; primResultTy)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

Var : Set
Var = ℕ

Label : Set
Label = ℕ

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·[_]_
infixl 7 _`[_]
infixl 6 _⊕[_at_]_
infix  9 `_

data GTerm : TyCtx → Set where
  `_      : ∀ {Δ} → Var → GTerm Δ
  ƛ_⇒_    : ∀ {Δ} → Ty Δ → GTerm Δ → GTerm Δ
  _·[_]_  : ∀ {Δ} → GTerm Δ → Label → GTerm Δ → GTerm Δ
  Λ_      : ∀ {Δ} → GTerm (suc Δ) → GTerm Δ
  _`[_]   : ∀ {Δ} → GTerm Δ → Ty Δ → GTerm Δ
  $       : ∀ {Δ} → Const → GTerm Δ
  _⊕[_at_]_ : ∀ {Δ}
    → GTerm Δ → Prim → Label → GTerm Δ → GTerm Δ

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

renameᵗᴳ : ∀ {Δ Δ′} → Δ ⇒ʳ Δ′ → GTerm Δ → GTerm Δ′
renameᵗᴳ ρ (` x) = ` x
renameᵗᴳ ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗᴳ ρ M
renameᵗᴳ ρ (L ·[ ℓ ] M) = renameᵗᴳ ρ L ·[ ℓ ] renameᵗᴳ ρ M
renameᵗᴳ ρ (Λ M) = Λ (renameᵗᴳ (extᵗ ρ) M)
renameᵗᴳ ρ (M `[ A ]) = renameᵗᴳ ρ M `[ renameᵗ ρ A ]
renameᵗᴳ ρ ($ κ) = $ κ
renameᵗᴳ ρ (L ⊕[ op at ℓ ] M) =
  renameᵗᴳ ρ L ⊕[ op at ℓ ] renameᵗᴳ ρ M

⇑ᵗᴳ : ∀ {Δ} → GTerm Δ → GTerm (suc Δ)
⇑ᵗᴳ = renameᵗᴳ Fin.suc

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value {Δ : TyCtx} : GTerm Δ → Set where
  ƛ_⇒_ : (A : Ty Δ) (N : GTerm Δ) → Value (ƛ A ⇒ N)
  $ : (κ : Const) → Value ($ κ)
  Λ_ : (N : GTerm (suc Δ)) → Value (Λ N)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ (Δ : TyCtx) (Γ : TermCtx Δ) :
    GTerm Δ → Ty Δ → Set where

  ⊢` : ∀ {x A}
    → Γ ∋ x ⦂ A
      ----------------------
    → Δ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
    → Δ ∣ (A ∷ Γ) ⊢ M ⦂ B
      --------------------------
    → Δ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A A′ B ℓ}
    → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
    → Δ ∣ Γ ⊢ M ⦂ A′
    → A ∼ A′
      -------------------------
    → Δ ∣ Γ ⊢ L ·[ ℓ ] M ⦂ B

  ⊢·★ : ∀ {L M A′ ℓ}
    → Δ ∣ Γ ⊢ L ⦂ ★
    → Δ ∣ Γ ⊢ M ⦂ A′
    → A′ ∼ ★
      -------------------------
    → Δ ∣ Γ ⊢ L ·[ ℓ ] M ⦂ ★

  ⊢Λ : ∀ {M A} {zero∈A : zero ∈ᵗ A}
    → Value M
    → (suc Δ) ∣ ⇑ᶜ Γ ⊢ M ⦂ A
      ------------------------
    → Δ ∣ Γ ⊢ Λ M ⦂ (`∀ A)

  ⊢• : ∀ {M B A}
    → Δ ∣ Γ ⊢ M ⦂ (`∀ B)
      ---------------------------
    → Δ ∣ Γ ⊢ M `[ A ] ⦂ B [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      ---------------------------
    → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B ℓ}
    → (op : Prim)
    → Δ ∣ Γ ⊢ L ⦂ A
    → A ∼ primArgTy op
    → Δ ∣ Γ ⊢ M ⦂ B
    → B ∼ primArgTy op
      -----------------------------------------------
    → Δ ∣ Γ ⊢ L ⊕[ op at ℓ ] M ⦂ primResultTy op
