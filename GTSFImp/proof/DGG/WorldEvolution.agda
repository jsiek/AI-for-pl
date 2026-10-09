{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolution where

-- File Charter:
--   * Defines endpoint-indexed one-step world evolution for trusted store
--     changes without placing applyStore or another defined function in a
--     data-constructor index.
--   * Separates constructor-form endpoint change from its executable store
--     and term-context projections.
--   * Covers keep, left-only, left-allocation-plus-alignment, right-only,
--     paired-precise, and paired-dynamic allocation as live World changes.
--   * Exports CtxChange, WorldEvolution, and their endpoint projections;
--     depends on World and the preservation context action.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-comp; renameᵗ-cong)
open import TyStore using (TyStore; store-bind; lookupStore)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.TypeSafety.Preservation using (applyTermCtx)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑)
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

  evolution-bind-left-aligned : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴿ : TyVar Δᴿ}
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (update : PivotUpdateᵗ
        (ηᴸᶜ (W ▻ᶜ bind-left-changeᶜ A eqᴸ)) Fin.zero
        (toRenameⁱ
          (ηᴿᶜ (W ▻ᶜ bind-left-changeᶜ A eqᴸ)) Xᴿ))
    → (boundary : AlignmentBoundaryᶜ
        (W ▻ᶜ bind-left-changeᶜ A eqᴸ) Fin.zero Xᴿ update)
    → (represented :
        (＇ Fin.zero) ⊑ᵀ⟨ W ▻ᶜ bind-left-changeᶜ A eqᴸ ⟩
          lookupStore Σᴿ Xᴿ)
    → WorldEvolution
        {W = W}
        {W′ =
          (W ▻ᶜ bind-left-changeᶜ A eqᴸ) ▻ᶜ
            rebase-source-changeᶜ Fin.zero Xᴿ update
              (alignment-onlyᶜ boundary) represented}
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


evolution-no-open-frames : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
  → WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ
  → openFramesᶜ W ≡ []
  → openFramesᶜ W′ ≡ []
evolution-no-open-frames evolution-keep no-open = no-open
evolution-no-open-frames (evolution-bind-left eqᴸ) no-open
    rewrite no-open = refl
evolution-no-open-frames
    (evolution-bind-left-aligned
      eqᴸ update boundary represented) no-open
    rewrite no-open = refl
evolution-no-open-frames
    (evolution-bind-right fresh eqᴿ) no-open
    rewrite no-open = refl
evolution-no-open-frames
    (evolution-bind-both represented eqᴸ eqᴿ) no-open
    rewrite no-open = refl
evolution-no-open-frames
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ) no-open
    rewrite no-open = refl


rename-shifted-off-zero : ∀ {Δᴸ Δᶜ}
    {η : Injectionᵗ (suc Δᴸ) Δᶜ}
    {Z : TyVar Δᶜ}
  → (update : PivotUpdateᵗ η Fin.zero Z)
  → (A : Ty Δᴸ)
  → renameᵗ (toRenameⁱ (pivot-afterᵗ update)) (⇑ᵗ A)
    ≡ renameᵗ (toRenameⁱ η) (⇑ᵗ A)
rename-shifted-off-zero {η = η} update A =
  trans (renameᵗ-comp Fin.suc
      (toRenameⁱ (pivot-afterᵗ update)) A)
    (trans
      (renameᵗ-cong A
        (λ X → off-pivot-fixedᵗ update (Fin.suc X) (λ ())))
      (sym (renameᵗ-comp Fin.suc (toRenameⁱ η) A)))


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
      renameᵗ (toRenameⁱ (skipⁱ (ηᴿᶜ W))) D)
    (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) C))
    (subst≡
      (λ T → marksᶜ (W ▻ᶜ bind-left-changeᶜ A eq) ⊢
        ⇑ᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ W)) C) ⊑ T)
      (sym (renameᵗ-skipⁱ (ηᴿᶜ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
evolution-⊑ᵀ {A = C} {B = D}
    (evolution-bind-left-aligned
      {A = A} {W = W} eq update boundary represented) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-left-changeᶜ A eq) ⊢ L ⊑
      renameᵗ
        (toRenameⁱ (ηᴿᶜ (W ▻ᶜ bind-left-changeᶜ A eq))) D)
    (sym (rename-shifted-off-zero update C))
    (evolution-⊑ᵀ
      (evolution-bind-left {A = A} {W = W} eq) p)
evolution-⊑ᵀ {A = C} {B = D}
    (evolution-bind-right {B = B} {W = W} fresh eq) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-right-changeᶜ B fresh eq) ⊢
      L ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W))) (⇑ᵗ D))
    (sym (renameᵗ-skipⁱ (ηᴸᶜ W) C))
    (subst≡
      (λ T → marksᶜ (W ▻ᶜ bind-right-changeᶜ B fresh eq) ⊢
        ⇑ᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ W)) C) ⊑ T)
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))
evolution-⊑ᵀ {A = A} {B = B}
    (evolution-bind-both {W = W} represented eqᴸ eqᴿ) p =
  subst≡
    (λ L → marksᶜ (W ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ)
      ⊢ L ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W))) (⇑ᵗ B))
    (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) A))
    (subst≡
      (λ T →
        marksᶜ (W ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ) ⊢
        ⇑ᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ W)) A) ⊑ T)
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))


evolution-⊑ᵀ {A = A} {B = B}
    (evolution-bind-both-star {W = W} represented A≠★ eqᴸ eqᴿ) p =
  subst≡
    (λ L → marksᶜ
      (W ▻ᶜ bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ) ⊢
      L ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W))) (⇑ᵗ B))
    (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) A))
    (subst≡
      (λ T → marksᶜ
        (W ▻ᶜ bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ) ⊢
        ⇑ᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ W)) A) ⊑ T)
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X mark → mark) p))


evolution-source-represented : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
    {Xᴸ : TyVar (CastTerms.Δᵉ Cᴸ)}
    {Xᴿ : TyVar (CastTerms.Δᵉ Cᴿ)}
  → (evolution : WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ)
  → (＇ Xᴸ) ⊑ᵀ⟨ W ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
  → (＇ R.applyVar (storeChange stepᴸ) Xᴸ) ⊑ᵀ⟨ W′ ⟩
      lookupStore (Σᵉ Cᴿ′)
        (R.applyVar (storeChange stepᴿ) Xᴿ)
evolution-source-represented evolution-keep represented = represented
evolution-source-represented
    evolution@(evolution-bind-left eqᴸ) represented =
  evolution-⊑ᵀ evolution represented
evolution-source-represented
    evolution@(evolution-bind-left-aligned
      eqᴸ update boundary aligned-represented) represented =
  evolution-⊑ᵀ evolution represented
evolution-source-represented
    evolution@(evolution-bind-right fresh eqᴿ) represented =
  evolution-⊑ᵀ evolution represented
evolution-source-represented
    evolution@(evolution-bind-both paired eqᴸ eqᴿ) represented =
  evolution-⊑ᵀ evolution represented
evolution-source-represented
    evolution@(evolution-bind-both-star paired A≠★ eqᴸ eqᴿ)
    represented =
  evolution-⊑ᵀ evolution represented


evolution-aligned : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
    {Xᴸ : TyVar (CastTerms.Δᵉ Cᴸ)}
    {Xᴿ : TyVar (CastTerms.Δᵉ Cᴿ)}
  → WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ
  → toRenameⁱ (ηᴸᶜ W) Xᴸ ≡ toRenameⁱ (ηᴿᶜ W) Xᴿ
  → toRenameⁱ (ηᴸᶜ W′) (R.applyVar (storeChange stepᴸ) Xᴸ)
    ≡ toRenameⁱ (ηᴿᶜ W′) (R.applyVar (storeChange stepᴿ) Xᴿ)
evolution-aligned evolution-keep aligned = aligned
evolution-aligned (evolution-bind-left eqᴸ) aligned =
  cong Fin.suc aligned
evolution-aligned {Xᴸ = Xᴸ}
    (evolution-bind-left-aligned
      eqᴸ update boundary represented) aligned =
  trans (off-pivot-fixedᵗ update (Fin.suc Xᴸ) (λ ()))
    (cong Fin.suc aligned)
evolution-aligned (evolution-bind-right fresh eqᴿ) aligned =
  cong Fin.suc aligned
evolution-aligned (evolution-bind-both represented eqᴸ eqᴿ) aligned =
  cong Fin.suc aligned
evolution-aligned
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ) aligned =
  cong Fin.suc aligned


evolution-source-mark : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
    {Xᴸ : TyVar (CastTerms.Δᵉ Cᴸ)} {v}
  → WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ
  → marksᶜ W (toRenameⁱ (ηᴸᶜ W) Xᴸ) ≡ v
  → marksᶜ W′
      (toRenameⁱ (ηᴸᶜ W′) (R.applyVar (storeChange stepᴸ) Xᴸ)) ≡ v
evolution-source-mark evolution-keep mark = mark
evolution-source-mark (evolution-bind-left eqᴸ) mark = mark
evolution-source-mark {Xᴸ = Xᴸ}
    (evolution-bind-left-aligned
      {A = A} {W = W} eqᴸ update boundary represented) mark =
  trans
    (cong (marksᶜ (W ▻ᶜ bind-left-changeᶜ A eqᴸ))
      (off-pivot-fixedᵗ update (Fin.suc Xᴸ) (λ ())))
    mark
evolution-source-mark (evolution-bind-right fresh eqᴿ) mark = mark
evolution-source-mark (evolution-bind-both represented eqᴸ eqᴿ) mark =
  mark
evolution-source-mark
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ) mark =
  mark


evolution-source-disaligned : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {stepᴸ : CtxChange Cᴸ Cᴸ′} {stepᴿ : CtxChange Cᴿ Cᴿ′}
    {Xᴸ : TyVar (CastTerms.Δᵉ Cᴸ)}
  → WorldEvolution {W = W} {W′ = W′} stepᴸ stepᴿ
  → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ W) Xᴿ ≢ toRenameⁱ (ηᴸᶜ W) Xᴸ)
  → ∀ Xᴿ′ → toRenameⁱ (ηᴿᶜ W′) Xᴿ′
      ≢ toRenameⁱ (ηᴸᶜ W′) (R.applyVar (storeChange stepᴸ) Xᴸ)
evolution-source-disaligned evolution-keep free = free
evolution-source-disaligned (evolution-bind-left eqᴸ) free Xᴿ aligned =
  free Xᴿ (fin-suc-injective aligned)
evolution-source-disaligned {Xᴸ = Xᴸ}
    (evolution-bind-left-aligned
      eqᴸ update boundary represented) free Xᴿ aligned =
  free Xᴿ
    (fin-suc-injective
      (trans aligned
        (off-pivot-fixedᵗ update (Fin.suc Xᴸ) (λ ()))))
evolution-source-disaligned
    (evolution-bind-right fresh eqᴿ) free Fin.zero ()
evolution-source-disaligned
    (evolution-bind-right fresh eqᴿ) free (Fin.suc Xᴿ) aligned =
  free Xᴿ (fin-suc-injective aligned)
evolution-source-disaligned
    (evolution-bind-both represented eqᴸ eqᴿ) free Fin.zero ()
evolution-source-disaligned
    (evolution-bind-both represented eqᴸ eqᴿ)
    free (Fin.suc Xᴿ) aligned =
  free Xᴿ (fin-suc-injective aligned)
evolution-source-disaligned
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ)
    free Fin.zero ()
evolution-source-disaligned
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ)
    free (Fin.suc Xᴿ) aligned =
  free Xᴿ (fin-suc-injective aligned)
