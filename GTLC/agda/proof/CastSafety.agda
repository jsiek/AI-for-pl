module proof.CastSafety where

-- File Charter:
--   * Private cast-calculus type-safety theorem.
--   * Used by GTLC type safety through compilation.

open import Agda.Builtin.List using ([])
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Types
open import CastCalculus
open import proof.CastCalculusMeta

type-safetyᶜ
  : {M N : Termᶜ} {A : Ty}
  → [] ⊢ᶜ M ⦂ A
  → M —↠ᶜ N
  → (∃[ N′ ] (N —→ᶜ N′)) ⊎ Result N
type-safetyᶜ M⦂A M—↠N with progressᶜ (preserveᶜ* M⦂A M—↠N)
... | step N→N′ = inj₁ (_ , N→N′)
... | done vN = inj₂ (r-val _ vN)
... | crash refl = inj₂ r-blame
