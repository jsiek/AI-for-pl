module proof.PreservationBetaDownNu where

-- File Charter:
--   * Worker file for the PolyConvert β-down-ν preservation redex.
--   * Opens the ν-bound imprecision evidence at the freshly allocated seal
--     and types the final reveal conversion from that seal back to the
--     type-application instantiation.
--   * Relies on shared type, imprecision, and conversion property modules;
--     does not depend on the store-threaded preservation induction hypothesis.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym)

open import Types
open import proof.TypeProperties using
  ( TySubstWf
  ; WfTy-weakenˢ
  ; singleTyEnv-Wf
  )
open import Store using (StoreWf; drop; ⊆ˢ-refl)
open import Imprecision
open import Conversion
open import Terms
open import proof.ConversionProperties using (convert↑At-wt)
open import proof.ImprecisionProperties using (length-plains[]; open-fresh-ν⊑)
open import proof.StoreProperties using (len<suc-StoreWf)
open import proof.TermProperties using (wk-term)

------------------------------------------------------------------------
-- β-down-ν preservation
------------------------------------------------------------------------

preserve-β-down-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B C : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (`∀A⊑B B p)) ⦂∀ C [ A ]) ⦂ C [ A ]ᵗ →
  Δ ∣ suc Ψ ∣ ((length Σ , A) ∷ Σ) ∣ Γ ⊢
    ((V ⇓ (p [ ｀ (length Σ) ]⊑)) ↑
      (convert↑ (src⊑ p) (length Σ))) ⦂ C [ A ]ᵗ
preserve-β-down-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  {V = V} {A = A} {C = C} {p = p} wfΣ vV
  (⊢• (⊢down (⊑-ν {A = Aν} {B = Bν} wfB p⊢) V⊢)
      wfC wfA) =
  cong-⊢⦂ refl refl refl
    (cong (λ B → B [ A ]ᵗ) (src⊑-correct p⊢))
    (⊢reveal c⊢ inner⊢)
  where
    len = length Σ

    top : ((len , A) ∷ Σ) ∋ˢ len ⦂ A
    top = Z∋ˢ refl refl

    hSeal :
      TySubstWf (suc Δ) Δ (suc Ψ)
        (substVarFrom zero (｀ len))
    hSeal =
      singleTyEnv-Wf (｀ len) (wfSeal (len<suc-StoreWf wfΣ))

    hA :
      TySubstWf (suc Δ) Δ (suc Ψ)
        (substVarFrom zero A)
    hA =
      singleTyEnv-Wf A (WfTy-weakenˢ wfA (n≤1+n Ψ))

    wf-src :
      WfTy (suc Δ) (suc Ψ) (src⊑ p)
    wf-src =
      WfTy-weakenˢ
        (subst
          (λ B → WfTy (suc Δ) Ψ B)
          (sym (src⊑-correct p⊢))
          (subst
            (λ n → WfTy n Ψ Aν)
            (cong suc (length-plains[] Δ))
            (⊑-src-wf p⊢)))
        (n≤1+n Ψ)

    c⊢ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ⊢
        convert↑ (src⊑ p) len ⦂
        (src⊑ p [ ｀ len ]ᵗ) ↑ˢ (src⊑ p [ A ]ᵗ)
    c⊢ = convert↑At-wt hSeal hA top wf-src

    p⊢′ :
      suc Ψ ∣ plains Δ [] ⊢ p [ ｀ len ]⊑ ⦂
        (Aν [ ｀ len ]ᵗ) ⊑ Bν
    p⊢′ = open-fresh-ν⊑ wfΣ p⊢

    V⊢′ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ∣ Γ ⊢ V ⦂ Bν
    V⊢′ = wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢

    inner⊢ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ∣ Γ ⊢
        V ⇓ (p [ ｀ len ]⊑) ⦂ src⊑ p [ ｀ len ]ᵗ
    inner⊢ =
      cong-⊢⦂ refl refl refl
        (cong (λ B → B [ ｀ len ]ᵗ) (sym (src⊑-correct p⊢)))
        (⊢down p⊢′ V⊢′)
