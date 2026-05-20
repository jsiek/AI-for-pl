module proof.PreservationBetaUpNu where

-- File Charter:
--   * Standalone preservation proof slice for the store-allocating β-up-ν
--     redex in PolyConvert.
--   * Uses fresh-ν imprecision opening from `proof.ImprecisionProperties`.
--   * Depends on seal/store weakening for terms, but not on the
--     store-threaded preservation induction hypothesis.

open import Data.List using (_∷_; length)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; refl; subst; sym)

open import Types
open import proof.TypeProperties using
  ( WfTy-weakenˢ )
open import Store
open import Imprecision
open import Terms
open import proof.ImprecisionProperties using
  (cong-⊢⊑; length-extend-X⊑X[]; open-fresh-ν⊑; src⊑-correct; ⊑-src-wf)
open import proof.StoreProperties using (len<suc-StoreWf)
open import proof.TermProperties using (wk-term)

------------------------------------------------------------------------
-- β-up-ν preservation
------------------------------------------------------------------------

preserve-β-up-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⇑ (∀A-⊑-B B p) ⦂ A →
  Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ ⊢
    ((V ⦂∀ (src⊑ p) [ ｀ (length Σ) ]) ⇑
      (p [ ｀ (length Σ) ]⊑)) ⦂ A
preserve-β-up-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {V = V} {p = p} wfΣ vV
  (⊢up (⊢∀A-⊑-B {A = Aν} wfB p⊢) V⊢) =
  ⊢up
    (cong-⊢⊑
      (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym (src⊑-correct p⊢)))
      refl
      (open-fresh-ν⊑ wfΣ p⊢))
    (⊢• V⊢′
      (WfTy-weakenˢ wf-src (n≤1+n Ψ))
      (wfSeal (len<suc-StoreWf wfΣ)))
  where
    wf-src : WfTy (suc Δ) Ψ (src⊑ p)
    wf-src =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym (src⊑-correct p⊢))
        (subst
          (λ n → WfTy n Ψ Aν)
          (cong suc (length-extend-X⊑X[] Δ))
          (⊑-src-wf p⊢))

    V⊢↑ :
      _ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ _ ⊢ V ⦂ `∀ _
    V⊢↑ = wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢

    V⊢′ :
      _ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ _ ⊢
      V ⦂ `∀ (src⊑ p)
    V⊢′ =
      cong-⊢⦂ refl refl refl
        (cong `∀ (sym (src⊑-correct p⊢)))
        V⊢↑
