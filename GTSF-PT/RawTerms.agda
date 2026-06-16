-- File Charter:
--   * Well-scoped raw terms used as the input syntax for type checking.
--   * Primary exports are raw expression contexts, raw variables, and raw terms.
--   * Depends on labels and core type syntax.

module RawTerms where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; Side; inside; outside)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Vec using ([] ; _∷_)

open import Label
open import Types

-- well-scoped terms

ExCtx = ℕ

ExVar : ExCtx → Set
ExVar = Fin

_▷ : ExCtx → ExCtx
_▷ = suc

data Ex (Δ : TyCtx) (Γ : ExCtx) : Set where

  `_ : ExVar Γ → Ex Δ Γ

  cst : (b : Σ Base base-type) → Ex Δ Γ

  λx:_⇒ : ∀ (T : Ty Δ) → Ex Δ (Γ ▷) → Ex Δ Γ

  app : (ℓ : Label) → Ex Δ Γ → Ex Δ Γ → Ex Δ Γ

  ΛX : Ex (Δ ▷) Γ → Ex Δ Γ

  tapp : (ℓ : Label) → Ex Δ Γ → (U : Ty Δ) → Ex Δ Γ
