module proof.PreservationBetaDownForall where

-- File Charter:
--   * Worker proof file for the PolyConvert β-down-∀ preservation redex.
--   * Opens the ∀-bound imprecision evidence with a fresh seal and proves
--     that `convert↑At` converts the opened source body from the fresh seal
--     endpoint to the original type-instantiation endpoint.
--   * Does not depend on the store-threaded preservation induction hypothesis.

open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_<_; _≤_; suc; zero; z<s; s<s)
open import Data.Nat.Properties using (_≟_; <-≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym; trans)

open import Types
open import proof.TypeProperties using
  ( TySubstWf
  ; TySubstWf-exts
  ; singleTyEnv-Wf
  ; WfTy-weakenˢ
  ; substᵗ-ground
  ; substᵗ-preserves-WfTy
  )
open import Store
open import Imprecision
open import Conversion
open import Terms
open import proof.ConversionProperties using (convert↑-fresh-wt)
open import proof.ImprecisionProperties
  using
    ( cong-⊢⊑
    ; length-extend-X⊑X[]
    ; open-fresh-∀⊑
    ; src⊑-correct
    ; tgt⊑-correct
    ; ⊑-src-wf
    ; ⊑-tgt-wf
    )
open import proof.StoreProperties using (len<suc-StoreWf)
open import proof.TermProperties using (wk-term)

------------------------------------------------------------------------
-- β-down-∀ preservation
------------------------------------------------------------------------

preserve-β-down-∀ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (‵∀ p)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
  Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢
    (((V ⦂∀ (tgt⊑ p) [ ｀ (length Σ) ]) ⇓
      (p [ ｀ (length Σ) ]⊑)) ↑ (convert↑ (src⊑ p) (length Σ)))
    ⦂ B [ T ]ᵗ
preserve-β-down-∀ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {V = V} {T = T} {p = p}
  wfΣ vV
  (⊢• (⊢down (⊢∀A-⊑-∀B {A = Aₚ} {B = Bₚ} p⊢) V⊢) wfB wfT) =
  cong-⊢⦂ refl refl refl (cong (λ A → A [ T ]ᵗ) eq-src)
    (⊢reveal c⊢ (⊢down p-open⊢ app⊢))
  where
    eq-src = src⊑-correct p⊢
    eq-tgt = tgt⊑-correct p⊢

    wf-src : WfTy (suc Δ) Ψ (src⊑ p)
    wf-src =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym eq-src)
        (subst
          (λ n → WfTy n Ψ Aₚ)
          (cong suc (length-extend-X⊑X[] Δ))
          (⊑-src-wf p⊢))

    wf-tgt : WfTy (suc Δ) Ψ (tgt⊑ p)
    wf-tgt =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym eq-tgt)
        (subst
          (λ n → WfTy n Ψ Bₚ)
          (cong suc (length-extend-X⊑X[] Δ))
          (⊑-tgt-wf p⊢))

    V⊢′ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ _ ⊢ V ⦂ `∀ (tgt⊑ p)
    V⊢′ =
      cong-⊢⦂ refl refl refl (cong `∀ (sym eq-tgt))
        (wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢)

    app⊢ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ _ ⊢
      V ⦂∀ tgt⊑ p [ ｀ (length Σ) ] ⦂
      tgt⊑ p [ ｀ (length Σ) ]ᵗ
    app⊢ =
      ⊢•
        V⊢′
        (WfTy-weakenˢ wf-tgt (n≤1+n Ψ))
        (wfSeal (len<suc-StoreWf wfΣ))

    p-open⊢ :
      suc Ψ ∣ extend-X⊑X Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
      tgt⊑ p [ ｀ (length Σ) ]ᵗ ⊒
      src⊑ p [ ｀ (length Σ) ]ᵗ
    p-open⊢ =
      cong-⊢⊑
        (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym eq-src))
        (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym eq-tgt))
        (open-fresh-∀⊑ wfΣ p⊢)

    c⊢ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ⊢
      convert↑ (src⊑ p) (length Σ) ⦂
      src⊑ p [ ｀ (length Σ) ]ᵗ ↑ˢ src⊑ p [ T ]ᵗ
    c⊢ = convert↑-fresh-wt wfΣ wf-src wfT
