{-# OPTIONS --allow-unsolved-metas #-}
module Compile where

-- File Charter:
--   * Compilation from gradual extrinsic terms to explicit-cast terms.
--   * Exports `compile` and `compile-value`.
--   * Depends on gradual term typing, consistency coercions, and type
--     well-formedness weakening.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _,_; proj₁)

open import Types
open import Ctx
open import Consistency
open import GradualTerms
open import Terms using (Term)
open import Terms
  renaming
    ( `_ to `ᵀ_
    ; ƛ_⇒_ to ƛᵀ_⇒_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; _⦂∀_[_] to _⦂∀ᵀ_[_]
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⇑_ to _⇑ᵀ_
    ; _⇓_ to _⇓ᵀ_
    ; Value to Valueᵀ
    ; _∣_∣_∣_⊢_⦂_ to _∣_∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢• to ⊢ᵀ•
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢up to ⊢ᵀup
    ; ⊢down to ⊢ᵀdown
    )
open import proof.ImprecisionConsistent using (coerce-wt-plains)
open import proof.TypeProperties using (WfTy-closed-weakenᵗ)

compile :
  ∀ {Δ Γ M A} →
  Δ ∣ Γ ⊢ M ⦂ A →
  Σ[ N ∈ Term ] Δ ∣ 0 ∣ [] ∣ Γ ⊢ᵀ N ⦂ A

compile-value :
  ∀ {Δ Γ M A} →
  (vM : Value M) →
  (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) →
  Valueᵀ (proj₁ (compile M⊢))

compile (⊢` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile (⊢ƛ wfA M⊢) with compile M⊢
compile (⊢ƛ wfA M⊢) | N , N⊢ =
  ƛᵀ _ ⇒ N , ⊢ᵀƛ wfA N⊢
compile (⊢· L⊢ M⊢ A~A′)
    with compile L⊢ | compile M⊢ | coerce-wt-plains A~A′
compile (⊢· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  L′ ·ᵀ ((M′ ⇓ᵀ coerce-⊑ A~A′) ⇑ᵀ coerce-⊒ A~A′) ,
  ⊢ᵀ· L′⊢ (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ M′⊢))
compile (⊢·★ L⊢ M⊢ A′~★)
    with compile L⊢ | compile M⊢
       | coerce-wt-plains (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★))
compile (⊢·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  ((L′ ⇓ᵀ coerce-⊑ (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★)))
    ⇑ᵀ coerce-⊒ (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★))) ·ᵀ M′ ,
  ⊢ᵀ· (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ L′⊢)) M′⊢
compile (⊢Λ vM M⊢) with compile M⊢ | compile-value vM M⊢
compile (⊢Λ vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ vN N⊢
compile (⊢• M⊢ wfB wfT) with compile M⊢
compile (⊢• {B = B} {T = T} M⊢ wfB wfT) | M′ , M′⊢ =
  M′ ⦂∀ᵀ B [ T ] , ⊢ᵀ• M′⊢ wfB wfT
compile {Δ = Δ} (⊢•★ M⊢ wfT)
    with compile M⊢
       | coerce-wt-plains (∀-~-B {Γ = boths Δ []} wf★ ★-~-★)
compile {Δ = Δ} (⊢•★ {T = T} M⊢ wfT)
    | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  ((M′ ⇓ᵀ coerce-⊑ (∀-~-B {Γ = boths Δ []} wf★ ★-~-★))
    ⇑ᵀ coerce-⊒ (∀-~-B {Γ = boths Δ []} wf★ ★-~-★)) ⦂∀ᵀ ★ [ T ] ,
  ⊢ᵀ• (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ M′⊢)) wf★
    (WfTy-closed-weakenᵗ Δ wfT)
compile (⊢$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with compile L⊢ | compile M⊢ | coerce-wt-plains A~ℕ
       | coerce-wt-plains B~ℕ
compile (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | BL , pL⊒⊢ , pL⊑⊢
    | BM , pM⊒⊢ , pM⊑⊢ =
  ((L′ ⇓ᵀ coerce-⊒ A~ℕ) ⇑ᵀ coerce-⊑ A~ℕ) ⊕ᵀ[ op ]
    ((M′ ⇓ᵀ coerce-⊒ B~ℕ) ⇑ᵀ coerce-⊑ B~ℕ) ,
  ⊢ᵀ⊕ (⊢ᵀup pL⊑⊢ (⊢ᵀdown pL⊒⊢ L′⊢)) op
       (⊢ᵀup pM⊑⊢ (⊢ᵀdown pM⊒⊢ M′⊢))

compile-value (ƛ A ⇒ M) (⊢ƛ wfA M⊢) = ƛᵀ A ⇒ proj₁ (compile M⊢)
compile-value ($ κ) (⊢$ .κ) = $ᵀ κ
compile-value (Λ M) (⊢Λ vM M⊢) = Λᵀ proj₁ (compile M⊢)
