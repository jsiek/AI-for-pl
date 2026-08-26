module alt.TenthBalancedExtensionProbe where

-- File Charter:
--   * Retains the tenth preservation obstruction found while screening U23's
--     strictly same-depth representation lookup, and checks its U24 repair.
--   * A closed value may cross an ambient anchor at depth zero.  Ordinary
--     beta substitution moves that value below a lexical type binder, where
--     U24's `≼-typ` now transports the representation by pure weakening, so
--     the very same contractum is typable.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

tenth-Ψ : TyEnv 1 0
tenth-Ψ = ∅ ,:= ‵ `ℕ

tenth-A : Ty 0
tenth-A = `∀ (‵ `ℕ)

tenth-interior : Term 1 1
tenth-interior = Λ ($ (κℕ 7))

tenth-interior-⊢ :
  tenth-Ψ ,begin[ zero ≔ zero ] ∣ [] ⊢ tenth-interior ⦂ `∀ (‵ `ℕ)
tenth-interior-⊢ = ⊢Λ (⊢$ (κℕ 7))

tenth-interior-value : Value tenth-interior
tenth-interior-value = Λ ($ (κℕ 7))

tenth-V : Term 1 0
tenth-V = tenth-interior ↑[ zero ≔ zero ] (`∀↑ id↑)

tenth-V-⊢ : tenth-Ψ ∣ [] ⊢ tenth-V ⦂ tenth-A
tenth-V-⊢ =
  ⊢reveal (found ≼-refl) (⊢↑-∀ (⊢id↑ (‵ `ℕ))) tenth-interior-⊢

tenth-V-value : Value tenth-V
tenth-V-value =
  result-val tenth-interior-value ↑[ zero ≔ zero ] all

tenth-body : Term 1 0
tenth-body = Λ (` 0)

tenth-redex : Term 1 0
tenth-redex = (ƛ tenth-A ˙ tenth-body) · tenth-V

tenth-redex-⊢ :
  tenth-Ψ ∣ [] ⊢ tenth-redex ⦂ `∀ (⇑ᵗ tenth-A)
tenth-redex-⊢ = ⊢· (⊢ƛ (⊢Λ (⊢` Z))) tenth-V-⊢

tenth-contractum : Term 1 0
tenth-contractum = tenth-body [ tenth-V ]

tenth-step : tenth-Ψ ⊢ tenth-redex —→ tenth-contractum
tenth-step = β tenth-V-value

-- U23 stopped here: the old relation had no constructor capable of ending at
-- the unmatched lexical entry below.  With lexical drift, the birth-to-query
-- path is exactly `≼-typ ≼-refl`, and its payload is weakened once.
tenth-contractum-⊢ :
  tenth-Ψ ∣ [] ⊢ tenth-contractum ⦂ `∀ (⇑ᵗ tenth-A)
tenth-contractum-⊢ =
  ⊢Λ (⊢reveal (found (≼-typ ≼-refl))
    (⊢↑-∀ (⊢id↑ (‵ `ℕ))) (⊢Λ (⊢$ (κℕ 7))))
