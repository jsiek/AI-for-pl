module LR.Precision where

-- File Charter:
--   * Two-context type precision for the logical-relation proof of the
--     dynamic gradual guarantee (notes/logrel-dgg.md; designed in
--     notes/denotational-dgg.md, Section 7a).
--     The left (more precise) type lives in Δ and the right one in Δ′.
--   * `Corr Δ Δ′` marks each left variable as
--       pair  paired with a right variable (X ⊑ Y),
--       only  left-only (X ⊑ ★), bound by a left-only `Λ` or `∀⊑`,
--       dead  occurring nowhere, bound by `∀⊑★`.
--     Every right variable is paired with exactly one left variable.
--   * The rules are `Imprecision`'s, except that `X ⊑ Y` needs a pair,
--     `X ⊑ ★` needs a left-only variable, and `∀⊑` does not shift the
--     right type.  The single-context relation `Imprecision` allows
--     `X ⊑ X` for every variable; that is what admits the `Catchup`
--     counterexample (notes, Section 8, risk 4).
--   * `embedᶜ Φ` embeds the right context into the left one, and
--     `impEnvᶜ Φ` is the single-context environment that `Φ` refines.

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision using (ImpEnv; VarImp; X⊑X; X⊑★)

------------------------------------------------------------------------
-- Variable correspondences
------------------------------------------------------------------------

data Corr : TyCtx → TyCtx → Set where
  []   : Corr zeroℕ zeroℕ
  pair : ∀ {Δ Δ′} → Corr Δ Δ′ → Corr (sucℕ Δ) (sucℕ Δ′)
  only : ∀ {Δ Δ′} → Corr Δ Δ′ → Corr (sucℕ Δ) Δ′
  dead : ∀ {Δ Δ′} → Corr Δ Δ′ → Corr (sucℕ Δ) Δ′

infix 4 _∋_↔_ _∋_only

-- X is paired with Y
data _∋_↔_ : ∀ {Δ Δ′} → Corr Δ Δ′ → TyVar Δ → TyVar Δ′ → Set where
  ↔-here : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} → pair Φ ∋ zero ↔ zero
  ↔-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y}
    → Φ ∋ X ↔ Y → pair Φ ∋ suc X ↔ suc Y
  ↔-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y}
    → Φ ∋ X ↔ Y → only Φ ∋ suc X ↔ Y
  ↔-dead : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y}
    → Φ ∋ X ↔ Y → dead Φ ∋ suc X ↔ Y

-- X is left-only
data _∋_only : ∀ {Δ Δ′} → Corr Δ Δ′ → TyVar Δ → Set where
  only-here : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} → only Φ ∋ zero only
  only-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X only → pair Φ ∋ suc X only
  only-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X only → only Φ ∋ suc X only
  only-dead : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X only → dead Φ ∋ suc X only

-- the embedding of the right context into the left one
embedᶜ : ∀ {Δ Δ′} → Corr Δ Δ′ → Δ′ ↪ᵗ Δ
embedᶜ [] = empty
embedᶜ (pair Φ) = keep (embedᶜ Φ)
embedᶜ (only Φ) = skip (embedᶜ Φ)
embedᶜ (dead Φ) = skip (embedᶜ Φ)

-- the single-context environment that Φ refines
impEnvᶜ : ∀ {Δ Δ′} → Corr Δ Δ′ → ImpEnv Δ
impEnvᶜ (pair Φ) zero = X⊑X
impEnvᶜ (pair Φ) (suc X) = impEnvᶜ Φ X
impEnvᶜ (only Φ) zero = X⊑★
impEnvᶜ (only Φ) (suc X) = impEnvᶜ Φ X
impEnvᶜ (dead Φ) zero = X⊑X
impEnvᶜ (dead Φ) (suc X) = impEnvᶜ Φ X

------------------------------------------------------------------------
-- Two-context type precision
------------------------------------------------------------------------

infix 4 _⊢_⊑_

data _⊢_⊑_ {Δ Δ′ : TyCtx} (Φ : Corr Δ Δ′) : Ty Δ → Ty Δ′ → Set where

  ★⊑★ :
      -------------
      Φ ⊢ ★ ⊑ ★

  ι⊑ι : ∀ {ι}
      ---------------------
    → Φ ⊢ ‵ ι ⊑ ‵ ι

  X⊑Y : ∀ {X Y}
    → Φ ∋ X ↔ Y
      -------------------
    → Φ ⊢ ＇ X ⊑ ＇ Y

  ⇒⊑⇒ : ∀ {A A′ B B′}
    → Φ ⊢ A ⊑ A′
    → Φ ⊢ B ⊑ B′
      ---------------------------
    → Φ ⊢ A ⇒ B ⊑ A′ ⇒ B′

  ∀⊑∀ : ∀ {A B}
    → pair Φ ⊢ A ⊑ B
      -----------------------
    → Φ ⊢ `∀ A ⊑ `∀ B

  ⇒⊑★ : ∀ {A B}
    → Φ ⊢ A ⊑ ★
    → Φ ⊢ B ⊑ ★
      -----------------
    → Φ ⊢ A ⇒ B ⊑ ★

  ι⊑★ : ∀ {ι}
      ---------------
    → Φ ⊢ ‵ ι ⊑ ★

  X⊑★ : ∀ {X}
    → Φ ∋ X only
      ----------------
    → Φ ⊢ ＇ X ⊑ ★

  ∀⊑ : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → only Φ ⊢ A ⊑ B
      ---------------------------
    → Φ ⊢ `∀ A ⊑ B

  ∀★⊑★ :
      ------------------
      Φ ⊢ `∀ ★ ⊑ ★

  ∀⊑★ : ∀ {A}
    → NonStar A
    → dead Φ ⊢ A ⊑ ★
      -----------------
    → Φ ⊢ `∀ A ⊑ ★

  bot-elim :
      --------------------------------
      Φ ⊢ `∀ (＇ zero) ⊑ `∀ ★

  bot⊑★ :
      ---------------------------
      Φ ⊢ `∀ (＇ zero) ⊑ ★
