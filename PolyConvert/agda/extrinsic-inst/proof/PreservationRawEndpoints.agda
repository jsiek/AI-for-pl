module proof.PreservationRawEndpoints where

-- File Charter:
--   * Endpoint well-formedness corollaries for raw preservation.
--   * Packages generic imprecision endpoint theorems for the `plains` contexts
--     used by β-up-∀ raw preservation.
--   * Depends only on type/imprecision endpoint facts and context lengths.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym)

open import Types
open import Imprecision

length-plains[] :
  ∀ Δ →
  length (plains Δ []) ≡ Δ
length-plains[] zero = refl
length-plains[] (suc Δ) = cong suc (length-plains[] Δ)

⊑-src-wf-plains :
  ∀ {Δ Ψ}{p : Imp}{A B : Ty} →
  Ψ ∣ (plain ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  WfTy (suc Δ) Ψ (src⊑ p)
⊑-src-wf-plains {Δ = Δ} {Ψ = Ψ} {A = A} p⊢ =
  subst
    (λ A′ → WfTy (suc Δ) Ψ A′)
    (sym (src⊑-correct p⊢))
    (subst
      (λ n → WfTy n Ψ A)
      (cong suc (length-plains[] Δ))
      (⊑-src-wf p⊢))
