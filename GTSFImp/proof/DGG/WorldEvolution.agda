{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolution where

-- File Charter:
--   * Defines endpoint-indexed one-step world evolution for trusted store
--     changes without placing applyStore or another defined function in a
--     data-constructor index.
--   * Separates constructor-form endpoint change from its executable store
--     and term-context projections.
--   * Covers keep, left-only, right-only, paired-precise, and paired-dynamic
--     allocation as live World changes.
--   * Exports CtxChange, WorldEvolution, and their endpoint projections;
--     depends on World and the preservation context action.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyVar; ★; ⇑ᵗ; renameᵗ; renameᵗ-comp; renameᵗ-cong;
   renameᵗ-shift)
open import TyStore using (TyStore; store-bind)
open import Consistency using (_↪ᵗ_; toRenameᵗ; keep; skip)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.TypeSafety.Preservation using (applyTermCtx)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.World


data CtxChange : Ctx → Ctx → Set where
  keep-ctx : ∀ {C}
    → CtxChange C C

  bind-ctx : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
      {A : Ty Δ} {Γ⁺ : TermCtx (suc Δ)}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → CtxChange
        ⟨ Δ , Σ , Γ ⟩
        ⟨ suc Δ , store-bind Σ A , Γ⁺ ⟩


storeChange : ∀ {C C′}
  → CtxChange C C′
  → R.StoreChange (CastTerms.Δᵉ C) (CastTerms.Δᵉ C′)
storeChange keep-ctx = R.keep
storeChange (bind-ctx {A = A} eq) = R.bind A


ctx-change-store : ∀ {C C′} (step : CtxChange C C′)
  → Σᵉ C′ ≡ R.applyStore (storeChange step) (Σᵉ C)
ctx-change-store keep-ctx = refl
ctx-change-store (bind-ctx eq) = refl


ctx-change-term : ∀ {C C′} (step : CtxChange C C′)
  → Γᵉ C′ ≡ applyTermCtx (storeChange step) (Γᵉ C)
ctx-change-term keep-ctx = refl
ctx-change-term (bind-ctx eq) = eq


data WorldEvolution : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
  → CtxChange Cᴸ Cᴸ′
  → CtxChange Cᴿ Cᴿ′
  → Set where
  evolution-keep : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → WorldEvolution {W = W} {W′ = W} keep-ctx keep-ctx

  evolution-bind-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ bind-left-changeᶜ A eqᴸ}
        (bind-ctx eqᴸ) keep-ctx

  evolution-bind-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (fresh : RightBindFreshᶜ W B)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ bind-right-changeᶜ B fresh eqᴿ}
        keep-ctx (bind-ctx eqᴿ)

  evolution-bind-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ⟨ W ⟩ B)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ
          bind-both-changeᶜ represented eqᴸ eqᴿ}
        (bind-ctx eqᴸ) (bind-ctx eqᴿ)

  evolution-bind-both-star : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ⟨ W ⟩ B)
      (A≠★ : ⇑ᵗ A ≢ ★)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W}
        {W′ = W ▻ᶜ
          bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ}
        (bind-ctx eqᴸ) (bind-ctx eqᴿ)


empty-evolution : WorldEvolution
    {W = emptyᶜ} {W′ = emptyᶜ} keep-ctx keep-ctx
empty-evolution = evolution-keep


renameᵗ-skip-eq : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ (skip η)) A
    ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
renameᵗ-skip-eq η A =
  trans (renameᵗ-cong A (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))


renameᵗ-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
    ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
renameᵗ-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)


evolution-⊑ᵀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
    {A : Ty (CastTerms.Δᵉ Cᴸ)} {B : Ty (CastTerms.Δᵉ Cᴿ)}
  → WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ
  → A ⊑ᵀ⟨ W ⟩ B
  → R.applyTy (storeChange stepᴸ) A ⊑ᵀ⟨ W′ ⟩
      R.applyTy (storeChange stepᴿ) B
evolution-⊑ᵀ evolution-keep p = p
evolution-⊑ᵀ {A = C} {B = D}
    (evolution-bind-left {A = A} {W = W} eq) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-left-changeᶜ A eq) ⊢ L ⊑
      renameᵗ (toRenameᵗ (skip (ηᴿᶜ W))) D)
    (sym (renameᵗ-keep-shift (ηᴸᶜ W) C))
    (subst≡
      (λ T → marksᶜ (W ▻ᶜ bind-left-changeᶜ A eq) ⊢
        ⇑ᵗ (renameᵗ (toRenameᵗ (ηᴸᶜ W)) C) ⊑ T)
      (sym (renameᵗ-skip-eq (ηᴿᶜ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
evolution-⊑ᵀ {A = C} {B = D}
    (evolution-bind-right {B = B} {W = W} fresh eq) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-right-changeᶜ B fresh eq) ⊢
      L ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W))) (⇑ᵗ D))
    (sym (renameᵗ-skip-eq (ηᴸᶜ W) C))
    (subst≡
      (λ T → marksᶜ (W ▻ᶜ bind-right-changeᶜ B fresh eq) ⊢
        ⇑ᵗ (renameᵗ (toRenameᵗ (ηᴸᶜ W)) C) ⊑ T)
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
evolution-⊑ᵀ {A = A} {B = B}
    (evolution-bind-both {W = W} represented eqᴸ eqᴿ) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ)
      ⊢ L ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W))) (⇑ᵗ B))
    (sym (renameᵗ-keep-shift (ηᴸᶜ W) A))
    (subst≡
      (λ T →
        marksᶜ (W ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ) ⊢
        ⇑ᵗ (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) ⊑ T)
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
evolution-⊑ᵀ {A = A} {B = B}
    (evolution-bind-both-star {W = W} represented A≠★ eqᴸ eqᴿ) p =
  subst≡
    (λ L → marksᶜ
      (W ▻ᶜ bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ) ⊢
      L ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W))) (⇑ᵗ B))
    (sym (renameᵗ-keep-shift (ηᴸᶜ W) A))
    (subst≡
      (λ T → marksᶜ
        (W ▻ᶜ bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ) ⊢
        ⇑ᵗ (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) ⊑ T)
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
