module nu-cancel-id.Types where

-- File Charter:
--   * THE TYPE SYNTAX, read two ways.  A NAMED type (an annotation the
--     programmer writes) has variables that are NAME positions: `` ` X ``
--     is the X-th named representation variable, counting from the
--     newest (nu-cancel-id.Ctx, `_∋ⁿ_↦_`).  A RUNTIME type (the type
--     terms have) has variables that are REPRESENTATION variables: de
--     Bruijn indices into the store.  In both, `` `∀ A `` binds index 0.
--   * Renaming only (`renameᵗ`, `extᵗ`, `⇑ᵗ`): allocation shifts the
--     store, and that is the one action runtime types need here.
--   * The design: notes/CancelIdSketch.md in strong-rep-nu (νF₁ᶜ).

open import Data.Nat using (ℕ; zero; suc)

infixr 7 _⇒_

data Ty : Set where
  `_  : ℕ → Ty
  `ℕ  : Ty
  `𝔹  : Ty
  _⇒_ : Ty → Ty → Ty
  `∀  : Ty → Ty

Renameᵗ : Set
Renameᵗ = ℕ → ℕ

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero    = zero
extᵗ ρ (suc α) = suc (ρ α)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` α)   = ` (ρ α)
renameᵗ ρ `ℕ      = `ℕ
renameᵗ ρ `𝔹      = `𝔹
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc
