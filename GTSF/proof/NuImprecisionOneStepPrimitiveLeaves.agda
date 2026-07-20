{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepPrimitiveLeaves where

-- File Charter:
--   * Freezes the runtime views and non-crossed primitive leaves needed by
--     the indexed one-step dispatcher.
--   * Covers Nat-value inversion and the primitive blame roots that do not
--     require transporting an operand across the other operand's catch-up.
--   * Excludes delta and crossed ξ schedules.
--   * Contains exactly five intended leaf-proof holes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import ImprecisionWf using (idι)
open import NuReduction using
  ( blame-⊕₁
  ; blame-⊕₂
  ; keep
  ; pure-step
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  )
open import NuTermImprecision using (StoreImp; leftCtxⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; _∣_∣_⊢_⦂_
  ; no•-⊕
  ; ok-no
  ; ok-⊕₁
  ; ok-⊕₂
  ; $
  ; blame
  ; _⊕[_]_
  )
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; allocation-prefixᵀ
  ; κ⊑κᵀ
  ; nu-term-imprecision-source-typing
  )
open import TermTyping using (forget)
open import Types using (`ℕ; ‵_)
open import proof.NuImprecisionTargetBlameCatchup using
  (left-catchup-target-blameᵀ; value-not-target-blameᵀ)
open import proof.NuImprecisionSimulationCore using
  ( WeakOneStepIndexedOutcome
  ; indexed-outcome-source-blame
  )
open import proof.NuProgress using
  (canonical-ℕ; nv-const; runtime-value-no•)
open import proof.NuReductionDeterminism using (value-irreducible)
open import proof.ReductionProperties using
  (applyTerms-preserves-Value; ↠-trans; ⊕₁-↠; ⊕₂-↠)


private
  leftCtxⁱ-[] :
    ∀ {Φ Δᴸ Δᴿ} →
    leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} [] ≡ []
  leftCtxⁱ-[] = refl

  runtime-stepping-primitive-left-argument-no• :
    ∀ {L L₁ M χ} →
    RuntimeOK (L ⊕[ addℕ ] M) →
    L —→[ χ ] L₁ →
    No• M
  runtime-stepping-primitive-left-argument-no•
      (ok-no (no•-⊕ noL noM)) L→ = noM
  runtime-stepping-primitive-left-argument-no•
      (ok-⊕₁ okL noM) L→ = noM
  runtime-stepping-primitive-left-argument-no•
      (ok-⊕₂ vL noL okM) L→ =
    ⊥-elim (value-irreducible vL L→)

  runtime-primitive-left-value-no• :
    ∀ {L M} →
    RuntimeOK (L ⊕[ addℕ ] M) →
    Value L →
    No• L
  runtime-primitive-left-value-no•
      (ok-no (no•-⊕ noL noM)) vL = noL
  runtime-primitive-left-value-no•
      (ok-⊕₁ okL noM) vL = runtime-value-no• okL vL
  runtime-primitive-left-value-no•
      (ok-⊕₂ vL noL okM) vL′ = noL

  related-nat-constant-target-constantᵀ :
    ∀ {Φ Δᴸ Δᴿ m n}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ $ (κℕ m) ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    $ (κℕ m) ≡ $ (κℕ n)
  related-nat-constant-target-constantᵀ κ⊑κᵀ = refl
  related-nat-constant-target-constantᵀ
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    related-nat-constant-target-constantᵀ M⊑M′


runtime-⊕₁-viewᵀ :
  ∀ {L L′ L₁′ M M′ χ} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  RuntimeOK (L′ ⊕[ addℕ ] M′) →
  L′ —→[ χ ] L₁′ →
  (No• M × No• M′) ⊎
  (Value L × No• L × RuntimeOK M × No• M′)
runtime-⊕₁-viewᵀ
    (ok-no (no•-⊕ noL noM)) okL′M′ L′→ =
  inj₁
    (noM , runtime-stepping-primitive-left-argument-no• okL′M′ L′→)
runtime-⊕₁-viewᵀ
    (ok-⊕₁ okL noM) okL′M′ L′→ =
  inj₁
    (noM , runtime-stepping-primitive-left-argument-no• okL′M′ L′→)
runtime-⊕₁-viewᵀ
    (ok-⊕₂ vL noL okM) okL′M′ L′→ =
  inj₂
    (vL , noL , okM ,
      runtime-stepping-primitive-left-argument-no• okL′M′ L′→)


runtime-⊕₂-viewᵀ :
  ∀ {L L′ M M′} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  RuntimeOK (L′ ⊕[ addℕ ] M′) →
  Value L′ →
  (Value L × No• L × RuntimeOK M × No• L′) ⊎
  (RuntimeOK L × No• M × No• L′)
runtime-⊕₂-viewᵀ okLM okL′M′ vL′
    with runtime-primitive-left-value-no• okL′M′ vL′
runtime-⊕₂-viewᵀ
    (ok-no (no•-⊕ noL noM)) okL′M′ vL′ | noL′ =
  inj₂ (ok-no noL , noM , noL′)
runtime-⊕₂-viewᵀ
    (ok-⊕₁ okL noM) okL′M′ vL′ | noL′ =
  inj₂ (okL , noM , noL′)
runtime-⊕₂-viewᵀ
    (ok-⊕₂ vL noL okM) okL′M′ vL′ | noL′ =
  inj₁ (vL , noL , okM , noL′)


related-nat-value-target-constantᵀ :
  ∀ {Φ Δᴸ Δᴿ V n}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  V ≡ $ (κℕ n)
related-nat-value-target-constantᵀ {V = V} {n = n} vV V⊑κ
    with canonical-ℕ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ V ⦂ ‵ `ℕ)
        leftCtxⁱ-[]
        (forget
          (nu-term-imprecision-source-typing
            {γ = []} {M = V} {M′ = $ (κℕ n)}
            {A = ‵ `ℕ} {B = ‵ `ℕ} V⊑κ)))
related-nat-value-target-constantᵀ {V = V} {n = n} vV V⊑κ
    | nv-const V≡
    rewrite V≡ =
  related-nat-constant-target-constantᵀ V⊑κ


weak-one-step-⊕-left-blame-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L M}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = blame} {χ = keep} {ρ = ρ} idι
weak-one-step-⊕-left-blame-indexed-outcomeᵀ
    (ok-no (no•-⊕ noL noM)) L⊑blame
    with left-catchup-target-blameᵀ (ok-no noL) L⊑blame
weak-one-step-⊕-left-blame-indexed-outcomeᵀ
    (ok-no (no•-⊕ noL noM)) L⊑blame
    | χs , L↠blame =
  indexed-outcome-source-blame
    (↠-trans (⊕₁-↠ noM L↠blame)
      (↠-step (pure-step blame-⊕₁) ↠-refl))
weak-one-step-⊕-left-blame-indexed-outcomeᵀ
    (ok-⊕₁ okL noM) L⊑blame
    with left-catchup-target-blameᵀ okL L⊑blame
weak-one-step-⊕-left-blame-indexed-outcomeᵀ
    (ok-⊕₁ okL noM) L⊑blame
    | χs , L↠blame =
  indexed-outcome-source-blame
    (↠-trans (⊕₁-↠ noM L↠blame)
      (↠-step (pure-step blame-⊕₁) ↠-refl))
weak-one-step-⊕-left-blame-indexed-outcomeᵀ
    (ok-⊕₂ vL noL okM) L⊑blame =
  ⊥-elim (value-not-target-blameᵀ vL L⊑blame)


weak-one-step-⊕-right-blame-right-first-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L M}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = blame} {χ = keep} {ρ = ρ} idι
weak-one-step-⊕-right-blame-right-first-indexed-outcomeᵀ
    vL noL okM M⊑blame
    with left-catchup-target-blameᵀ okM M⊑blame
weak-one-step-⊕-right-blame-right-first-indexed-outcomeᵀ
    vL noL okM M⊑blame
    | χs , M↠blame =
  indexed-outcome-source-blame
    (↠-trans (⊕₂-↠ vL noL M↠blame)
      (↠-step
        (pure-step (blame-⊕₂ (applyTerms-preserves-Value χs vL)))
        ↠-refl))
