module alt.TenthBalancedExtensionProbe where

-- File Charter:
--   * Records the tenth preservation obstruction found while screening U23's
--     verbatim representation lookup.
--   * A closed value may cross an ambient anchor at depth zero.  Ordinary
--     beta substitution moves that value below a lexical type binder, where
--     its crossing is at depth one but its ambient representation birth is
--     still at depth zero.  The balanced lookup consequently refuses the
--     contractum, so closed-context preservation is false for this design.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

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

-- No balanced extension can end in an unmatched lexical marker.
no-birth-to-typ : ∀ {Θ Θ′ Δ k}
    {Ξ : TyEnv Θ (suc Δ)} {A : Ty (suc Δ)} {Φ : TyEnv Θ′ Δ}
  → (Ξ ,:= A) ≼[ k ] (Φ ,typ)
  → ⊥
no-birth-to-typ ()

no-rep-after-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {a : TyVar Θ} {C : Ty (suc Δ)}
  → Ψ ,typ ∋rep a ≔ C
  → ⊥
no-rep-after-typ (found extension) = no-birth-to-typ extension

tenth-contractum-untypable :
  tenth-Ψ ∣ [] ⊢ tenth-contractum ⦂ `∀ (⇑ᵗ tenth-A)
  → ⊥
tenth-contractum-untypable (⊢Λ (⊢reveal α∈ c⊢ M⊢)) =
  no-rep-after-typ α∈
