module proof.PreservationRawEndpoints where

-- File Charter:
--   * Endpoint well-formedness corollaries for raw preservation.
--   * Packages generic imprecision endpoint theorems for the `extend-X⊑X` contexts
--     used by β-up-∀ raw preservation.
--   * Depends only on type/imprecision endpoint facts and context lengths.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym)

open import Types
open import Imprecision
open import proof.ImprecisionProperties using (src⊑-correct; ⊑-src-wf)

length-extend-X⊑X[] :
  ∀ Δ →
  length (extend-X⊑X Δ []) ≡ Δ
length-extend-X⊑X[] zero = refl
length-extend-X⊑X[] (suc Δ) = cong suc (length-extend-X⊑X[] Δ)

⊑-src-wf-extend-X⊑X :
  ∀ {Δ Ψ}{p : Imp}{A B : Ty} →
  Ψ ∣ (X⊑X ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ B →
  WfTy (suc Δ) Ψ (src⊑ p)
⊑-src-wf-extend-X⊑X {Δ = Δ} {Ψ = Ψ} {A = A} p⊢ =
  subst
    (λ A′ → WfTy (suc Δ) Ψ A′)
    (sym (src⊑-correct p⊢))
    (subst
      (λ n → WfTy n Ψ A)
      (cong suc (length-extend-X⊑X[] Δ))
      (⊑-src-wf p⊢))
