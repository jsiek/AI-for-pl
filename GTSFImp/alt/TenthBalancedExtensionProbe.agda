module alt.TenthBalancedExtensionProbe where

-- File Charter:
--   * Retains the tenth preservation obstruction found while screening U23.
--   * The restored ΛBody restriction now excludes its captured-variable Λ
--     source, so the former beta/substitution trace is no longer reachable.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; nothing)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

tenth-Ψ : TyEnv 1 0 Vec.[]
tenth-Ψ = ∅ ,:= ‵ `ℕ

empty-fresh : ∀ {Θ} {a : TyVar Θ} → a ∉ᵛ Vec.[]
empty-fresh ()

nothing-fresh : ∀ {Θ} {a : TyVar Θ}
  → a ∉ᵛ (nothing Vec.∷ Vec.[])
nothing-fresh zero ()

tenth-A : Ty 0
tenth-A = `∀ (‵ `ℕ)

tenth-interior : Term 1 1
tenth-interior = Λ ($ (κℕ 7))

tenth-interior-⊢ :
  tenth-Ψ ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩ ∣ []
    ⊢ tenth-interior ⦂ `∀ (‵ `ℕ)
tenth-interior-⊢ =
  ⊢Λ (body-result (result-val ($ (κℕ 7)))) (⊢$ (κℕ 7))

tenth-interior-value : Value tenth-interior
tenth-interior-value = Λ (result-val ($ (κℕ 7)))

tenth-V : Term 1 0
tenth-V = tenth-interior ↑[ zero ≔ zero ] (`∀↑ id↑)

tenth-V-⊢ : tenth-Ψ ∣ [] ⊢ tenth-V ⦂ tenth-A
tenth-V-⊢ =
  ⊢reveal refl (⊢↑-∀ (⊢id↑ (‵ `ℕ))) tenth-interior-⊢

tenth-body-interior : Term 1 1
tenth-body-interior = ` 0

tenth-body-interior-not-admissible : ¬ ΛBody tenth-body-interior
tenth-body-interior-not-admissible (body-result (result-val ()))

tenth-body : Term 1 0
tenth-body = Λ tenth-body-interior

tenth-redex : Term 1 0
tenth-redex = (ƛ tenth-A ˙ tenth-body) · tenth-V

tenth-redex-not-typed :
  ¬ (tenth-Ψ ∣ [] ⊢ tenth-redex ⦂ `∀ (⇑ᵗ tenth-A))
tenth-redex-not-typed (⊢· (⊢ƛ (⊢Λ body M⊢)) V⊢) =
  tenth-body-interior-not-admissible body
