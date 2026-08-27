{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolutionSequence where

-- File Charter:
--   * Composes one-step two-Ctx world evolutions while retaining each
--     step's allocation evidence and explicit intermediate world.
--   * Keeps sequence constructors and variables in data indices; executable
--     store, context, and term transport occurs only in projection theorems.
--   * Covers unilateral scheduling as well as paired steps and checks the
--     final projections against trusted StoreChanges transport.
--   * Transports source conversion typing and generator positions to the
--     final world without packaging a replay action.
--   * Exports MultiWorldEvolution, request prepend operations, and final
--     store/context/term projections; depends on one-step evolution, its
--     request producer, and the preservation context action.

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst; cong; trans)

import TermCtx as TC
open import Types using (Ty; TyVar; TyCtx)
open import TyStore using (TyStore)
import Conversion as Conv
open import CastTerms using (Term; ⇑ᵗᵐ; Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
import Reduction as R
open R using (StoreChange; StoreChanges; []; _∷_)
open import proof.TypeSafety.Preservation using
  (applyTermCtx; applyTermCtxs; applyTermCtxs-id; applyTermCtxs-step)
open import proof.Reduction using
  (_++χ_; applyVars; applyReveals; applyConceals;
   applyReveals-⊢↑; applyConceals-⊢↓)
open import proof.DGG.ConversionPivotAlignment using
  ( revealGeneratorPosition
  ; concealGeneratorPosition
  ; revealGeneratorPosition-store-transport
  ; concealGeneratorPosition-store-transport
  ; revealGeneratorPosition-apply
  ; concealGeneratorPosition-apply
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolution
open import proof.DGG.WorldEvolutionProducer


data MultiWorldEvolution : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
  → StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)
  → StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)
  → Set where

  evolutions-refl : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → MultiWorldEvolution {W = W} {W′ = W} [] []

  evolutions-step-left : ∀
      {Cᴸ Cᴿ Cᴸ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ Cᴿ} {W¹ : Cᴸ¹ ⊑ᶜ Cᴿ}
      {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
      {χᴸ : StoreChange (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
      {stepᴸ : CtxChange Cᴸ Cᴸ¹}
    → storeChange stepᴸ ≡ χᴸ
    → WorldEvolution {W = W} {W′ = W¹} stepᴸ keep-ctx
    → MultiWorldEvolution {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolution {W = W} {W′ = W′}
        (χᴸ ∷ χsᴸ) χsᴿ

  evolutions-step-right : ∀
      {Cᴸ Cᴿ Cᴿ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ Cᴿ} {W¹ : Cᴸ ⊑ᶜ Cᴿ¹}
      {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
      {χᴿ : StoreChange (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ′)}
      {stepᴿ : CtxChange Cᴿ Cᴿ¹}
    → storeChange stepᴿ ≡ χᴿ
    → WorldEvolution {W = W} {W′ = W¹} keep-ctx stepᴿ
    → MultiWorldEvolution {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolution {W = W} {W′ = W′}
        χsᴸ (χᴿ ∷ χsᴿ)

  evolutions-step-both : ∀
      {Cᴸ Cᴿ Cᴸ¹ Cᴿ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ Cᴿ} {W¹ : Cᴸ¹ ⊑ᶜ Cᴿ¹}
      {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
      {χᴸ : StoreChange (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
      {χᴿ : StoreChange (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ′)}
      {stepᴸ : CtxChange Cᴸ Cᴸ¹}
      {stepᴿ : CtxChange Cᴿ Cᴿ¹}
    → storeChange stepᴸ ≡ χᴸ
    → storeChange stepᴿ ≡ χᴿ
    → WorldEvolution {W = W} {W′ = W¹} stepᴸ stepᴿ
    → MultiWorldEvolution {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolution {W = W} {W′ = W′}
        (χᴸ ∷ χsᴸ) (χᴿ ∷ χsᴿ)


multi-sourceRebaseCount : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → sourceRebaseCountᶜ W′ ≡ sourceRebaseCountᶜ W
multi-sourceRebaseCount evolutions-refl = refl
multi-sourceRebaseCount
    (evolutions-step-left eqᴸ evolution-keep tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-left eqᴸ (evolution-bind-left eq) tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-right eqᴿ evolution-keep tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-right eqᴿ (evolution-bind-right fresh eq) tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-both eqᴸ eqᴿ evolution-keep tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-both eqᴸ eqᴿ (evolution-bind-left eq) tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-both eqᴸ eqᴿ
      (evolution-bind-right fresh eq) tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-both eqᴸ eqᴿ
      (evolution-bind-both represented eqᴸ′ eqᴿ′) tail) =
  multi-sourceRebaseCount tail
multi-sourceRebaseCount
    (evolutions-step-both eqᴸ eqᴿ
      (evolution-bind-both-star represented A≠★ eqᴸ′ eqᴿ′) tail) =
  multi-sourceRebaseCount tail


multi-no-source-rebase : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → sourceRebaseCountᶜ W ≡ 0
  → sourceRebaseCountᶜ W′ ≡ 0
multi-no-source-rebase evol no-rebase =
  trans (multi-sourceRebaseCount evol) no-rebase


composeMultiWorldEvolution : ∀
    {Cᴸ Cᴿ Cᴸ¹ Cᴿ¹ Cᴸ² Cᴿ² : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W¹ : Cᴸ¹ ⊑ᶜ Cᴿ¹}
    {W² : Cᴸ² ⊑ᶜ Cᴿ²}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
    {ψsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ²)}
    {ψsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ²)}
  → MultiWorldEvolution {W = W} {W′ = W¹} χsᴸ χsᴿ
  → MultiWorldEvolution {W = W¹} {W′ = W²} ψsᴸ ψsᴿ
  → MultiWorldEvolution {W = W} {W′ = W²}
      (χsᴸ ++χ ψsᴸ) (χsᴿ ++χ ψsᴿ)
composeMultiWorldEvolution evolutions-refl second = second
composeMultiWorldEvolution
    (evolutions-step-left eqᴸ one tail) second =
  evolutions-step-left eqᴸ one
    (composeMultiWorldEvolution tail second)
composeMultiWorldEvolution
    (evolutions-step-right eqᴿ one tail) second =
  evolutions-step-right eqᴿ one
    (composeMultiWorldEvolution tail second)
composeMultiWorldEvolution
    (evolutions-step-both eqᴸ eqᴿ one tail) second =
  evolutions-step-both eqᴸ eqᴿ one
    (composeMultiWorldEvolution tail second)


append-left-keep : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolution {W = W} {W′ = W′}
      (χsᴸ ++χ (R.keep ∷ [])) χsᴿ
append-left-keep evolutions-refl =
  evolutions-step-left refl evolution-keep evolutions-refl
append-left-keep (evolutions-step-left eqᴸ one tail) =
  evolutions-step-left eqᴸ one (append-left-keep tail)
append-left-keep (evolutions-step-right eqᴿ one tail) =
  evolutions-step-right eqᴿ one (append-left-keep tail)
append-left-keep (evolutions-step-both eqᴸ eqᴿ one tail) =
  evolutions-step-both eqᴸ eqᴿ one (append-left-keep tail)


multi-⊑ᵀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → A ⊑ᵀ⟨ W ⟩ B
  → R.applyTys χsᴸ A ⊑ᵀ⟨ W′ ⟩ R.applyTys χsᴿ B
multi-⊑ᵀ evolutions-refl p = p
multi-⊑ᵀ (evolutions-step-left refl one tail) p =
  multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
multi-⊑ᵀ (evolutions-step-right refl one tail) p =
  multi-⊑ᵀ tail (evolution-⊑ᵀ one p)
multi-⊑ᵀ (evolutions-step-both refl refl one tail) p =
  multi-⊑ᵀ tail (evolution-⊑ᵀ one p)


applyVars-prepend : ∀ {C C¹ : Ctx} {Δ′ : TyCtx}
    (step : CtxChange C C¹)
    (χs : StoreChanges (Δᵉ C¹) Δ′)
    (X : TyVar (Δᵉ C))
  → applyVars (storeChange step ∷ χs) X
      ≡ applyVars χs (R.applyVar (storeChange step) X)
applyVars-prepend keep-ctx χs X = refl
applyVars-prepend (bind-ctx eq) χs X = refl


multi-aligned : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → toRenameⁱ (ηᴸᶜ W) Xᴸ ≡ toRenameⁱ (ηᴿᶜ W) Xᴿ
  → toRenameⁱ (ηᴸᶜ W′) (applyVars χsᴸ Xᴸ)
      ≡ toRenameⁱ (ηᴿᶜ W′) (applyVars χsᴿ Xᴿ)
multi-aligned evolutions-refl aligned = aligned
multi-aligned {Xᴸ = Xᴸ}
    (evolutions-step-left {χsᴸ = χsᴸ} {stepᴸ = stepᴸ}
      refl one tail) aligned
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ =
  multi-aligned tail (evolution-aligned one aligned)
multi-aligned {Xᴿ = Xᴿ}
    (evolutions-step-right {χsᴿ = χsᴿ} {stepᴿ = stepᴿ}
      refl one tail) aligned
    rewrite applyVars-prepend stepᴿ χsᴿ Xᴿ =
  multi-aligned tail (evolution-aligned one aligned)
multi-aligned {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (evolutions-step-both {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {stepᴸ = stepᴸ} {stepᴿ = stepᴿ} refl refl one tail)
    aligned
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ
          | applyVars-prepend stepᴿ χsᴿ Xᴿ =
  multi-aligned tail (evolution-aligned one aligned)


multi-source-mark : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {Xᴸ : TyVar (Δᵉ Cᴸ)} {v}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → marksᶜ W (toRenameⁱ (ηᴸᶜ W) Xᴸ) ≡ v
  → marksᶜ W′
      (toRenameⁱ (ηᴸᶜ W′) (applyVars χsᴸ Xᴸ)) ≡ v
multi-source-mark evolutions-refl mark = mark
multi-source-mark {Xᴸ = Xᴸ}
    (evolutions-step-left {χsᴸ = χsᴸ} {stepᴸ = stepᴸ}
      refl one tail) mark
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ =
  multi-source-mark tail (evolution-source-mark one mark)
multi-source-mark (evolutions-step-right refl one tail) mark =
  multi-source-mark tail (evolution-source-mark one mark)
multi-source-mark {Xᴸ = Xᴸ}
    (evolutions-step-both {χsᴸ = χsᴸ} {stepᴸ = stepᴸ}
      refl refl one tail) mark
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ =
  multi-source-mark tail (evolution-source-mark one mark)


multi-source-disaligned : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {Xᴸ : TyVar (Δᵉ Cᴸ)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ W) Xᴿ ≢ toRenameⁱ (ηᴸᶜ W) Xᴸ)
  → ∀ Xᴿ′ → toRenameⁱ (ηᴿᶜ W′) Xᴿ′
      ≢ toRenameⁱ (ηᴸᶜ W′) (applyVars χsᴸ Xᴸ)
multi-source-disaligned evolutions-refl free = free
multi-source-disaligned {Xᴸ = Xᴸ}
    (evolutions-step-left {χsᴸ = χsᴸ} {stepᴸ = stepᴸ}
      refl one tail) free
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ =
  multi-source-disaligned tail (evolution-source-disaligned one free)
multi-source-disaligned (evolutions-step-right refl one tail) free =
  multi-source-disaligned tail (evolution-source-disaligned one free)
multi-source-disaligned {Xᴸ = Xᴸ}
    (evolutions-step-both {χsᴸ = χsᴸ} {stepᴸ = stepᴸ}
      refl refl one tail) free
    rewrite applyVars-prepend stepᴸ χsᴸ Xᴸ =
  multi-source-disaligned tail (evolution-source-disaligned one free)


request-source-change : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → storeChange (evolutionSourceChange request) ≡ χᴸ
request-source-change evolution-request-keep = refl
request-source-change (evolution-request-left eqᴸ) = refl
request-source-change (evolution-request-right fresh eqᴿ) = refl
request-source-change
    (evolution-request-both-precise represented eqᴸ eqᴿ) = refl
request-source-change
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = refl


request-target-change : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → storeChange (evolutionTargetChange request) ≡ χᴿ
request-target-change evolution-request-keep = refl
request-target-change (evolution-request-left eqᴸ) = refl
request-target-change (evolution-request-right fresh eqᴿ) = refl
request-target-change
    (evolution-request-both-precise represented eqᴸ eqᴿ) = refl
request-target-change
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = refl


prepend-both-request : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ¹ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ¹ (Δᵉ Cᴿ′)}
  → MultiWorldEvolution
      {W = evolutionWorld request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolution {W = W} {W′ = W′}
      (χᴸ ∷ χsᴸ) (χᴿ ∷ χsᴿ)
prepend-both-request request tail =
  evolutions-step-both
    (request-source-change request)
    (request-target-change request)
    (produceWorldEvolution request) tail


prepend-left-request : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    (request : WorldEvolutionRequest W χᴸ R.keep)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ¹ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ (Δᵉ Cᴿ′)}
  → MultiWorldEvolution
      {W = evolutionWorld request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolution {W = W} {W′ = W′}
      (χᴸ ∷ χsᴸ) χsᴿ
prepend-left-request evolution-request-keep tail =
  evolutions-step-left refl evolution-keep tail
prepend-left-request (evolution-request-left eqᴸ) tail =
  evolutions-step-left refl (evolution-bind-left eqᴸ) tail


prepend-right-request : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴿ¹} {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequest W R.keep χᴿ)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ¹ (Δᵉ Cᴿ′)}
  → MultiWorldEvolution
      {W = evolutionWorld request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolution {W = W} {W′ = W′}
      χsᴸ (χᴿ ∷ χsᴿ)
prepend-right-request evolution-request-keep tail =
  evolutions-step-right refl evolution-keep tail
prepend-right-request
    (evolution-request-right fresh eqᴿ) tail =
  evolutions-step-right refl
    (evolution-bind-right fresh eqᴿ) tail


ctx-change-store-as : ∀ {C C¹ : Ctx}
    {step : CtxChange C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChange step ≡ χ
  → Σᵉ C¹ ≡ R.applyStore χ (Σᵉ C)
ctx-change-store-as {C = C} {step = step} eq =
  trans (ctx-change-store step)
    (cong (λ ψ → R.applyStore ψ (Σᵉ C)) eq)


ctx-change-term-as : ∀ {C C¹ : Ctx}
    {step : CtxChange C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChange step ≡ χ
  → Γᵉ C¹ ≡ applyTermCtx χ (Γᵉ C)
ctx-change-term-as {C = C} {step = step} eq =
  trans (ctx-change-term step)
    (cong (λ ψ → applyTermCtx ψ (Γᵉ C)) eq)


multi-source-store : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Σᵉ Cᴸ′ ≡ R.applyStores χsᴸ (Σᵉ Cᴸ)
multi-source-store evolutions-refl = refl
multi-source-store
    (evolutions-step-left {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) =
  trans (multi-source-store tail)
    (cong (R.applyStores χsᴸ) (ctx-change-store-as eqᴸ))
multi-source-store
    (evolutions-step-right eqᴿ one tail) =
  multi-source-store tail
multi-source-store
    (evolutions-step-both {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) =
  trans (multi-source-store tail)
    (cong (R.applyStores χsᴸ) (ctx-change-store-as eqᴸ))


multi-target-store : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Σᵉ Cᴿ′ ≡ R.applyStores χsᴿ (Σᵉ Cᴿ)
multi-target-store evolutions-refl = refl
multi-target-store
    (evolutions-step-left eqᴸ one tail) =
  multi-target-store tail
multi-target-store
    (evolutions-step-right {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) =
  trans (multi-target-store tail)
    (cong (R.applyStores χsᴿ) (ctx-change-store-as eqᴿ))
multi-target-store
    (evolutions-step-both {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) =
  trans (multi-target-store tail)
    (cong (R.applyStores χsᴿ) (ctx-change-store-as eqᴿ))


multi-source-reveal : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴸ)} {c : Conv.Conv↑ (Δᵉ Cᴸ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → Σᵉ Cᴸ Conv.⊢↑[ X ⦂ Rep ] c
  → Σᵉ Cᴸ′ Conv.⊢↑[
      applyVars χsᴸ X ⦂ R.applyTys χsᴸ Rep ] applyReveals χsᴸ c
multi-source-reveal {χsᴸ = χsᴸ} {X = X} {Rep = Rep} {c = c}
    evol c⊢ =
  subst
    (λ Σ → Σ Conv.⊢↑[
      applyVars χsᴸ X ⦂ R.applyTys χsᴸ Rep ] applyReveals χsᴸ c)
    (sym (multi-source-store evol))
    (applyReveals-⊢↑ {χs = χsᴸ} c⊢)


multi-source-conceal : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴸ)} {c : Conv.Conv↓ (Δᵉ Cᴸ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → Σᵉ Cᴸ Conv.⊢↓[ X ⦂ Rep ] c
  → Σᵉ Cᴸ′ Conv.⊢↓[
      applyVars χsᴸ X ⦂ R.applyTys χsᴸ Rep ] applyConceals χsᴸ c
multi-source-conceal {χsᴸ = χsᴸ} {X = X} {Rep = Rep} {c = c}
    evol c⊢ =
  subst
    (λ Σ → Σ Conv.⊢↓[
      applyVars χsᴸ X ⦂ R.applyTys χsᴸ Rep ] applyConceals χsᴸ c)
    (sym (multi-source-store evol))
    (applyConceals-⊢↓ {χs = χsᴸ} c⊢)


multi-source-reveal-position : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴸ)} {c : Conv.Conv↑ (Δᵉ Cᴸ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → (c⊢ : Σᵉ Cᴸ Conv.⊢↑[ X ⦂ Rep ] c)
  → revealGeneratorPosition
      (multi-source-reveal {χsᴸ = χsᴸ} evol c⊢)
      ≡ revealGeneratorPosition c⊢
multi-source-reveal-position {χsᴸ = χsᴸ} evol c⊢ =
  trans
    (revealGeneratorPosition-store-transport
      (sym (multi-source-store evol))
      (applyReveals-⊢↑ {χs = χsᴸ} c⊢))
    (revealGeneratorPosition-apply {χs = χsᴸ} c⊢)


multi-source-conceal-position : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴸ)} {c : Conv.Conv↓ (Δᵉ Cᴸ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → (c⊢ : Σᵉ Cᴸ Conv.⊢↓[ X ⦂ Rep ] c)
  → concealGeneratorPosition
      (multi-source-conceal {χsᴸ = χsᴸ} evol c⊢)
      ≡ concealGeneratorPosition c⊢
multi-source-conceal-position {χsᴸ = χsᴸ} evol c⊢ =
  trans
    (concealGeneratorPosition-store-transport
      (sym (multi-source-store evol))
      (applyConceals-⊢↓ {χs = χsᴸ} c⊢))
    (concealGeneratorPosition-apply {χs = χsᴸ} c⊢)


multi-target-reveal : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴿ)} {c : Conv.Conv↑ (Δᵉ Cᴿ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → Σᵉ Cᴿ Conv.⊢↑[ X ⦂ Rep ] c
  → Σᵉ Cᴿ′ Conv.⊢↑[
      applyVars χsᴿ X ⦂ R.applyTys χsᴿ Rep ] applyReveals χsᴿ c
multi-target-reveal {χsᴿ = χsᴿ} {X = X} {Rep = Rep} {c = c}
    evol c⊢ =
  subst
    (λ Σ → Σ Conv.⊢↑[
      applyVars χsᴿ X ⦂ R.applyTys χsᴿ Rep ] applyReveals χsᴿ c)
    (sym (multi-target-store evol))
    (applyReveals-⊢↑ {χs = χsᴿ} c⊢)


multi-target-conceal : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴿ)} {c : Conv.Conv↓ (Δᵉ Cᴿ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → Σᵉ Cᴿ Conv.⊢↓[ X ⦂ Rep ] c
  → Σᵉ Cᴿ′ Conv.⊢↓[
      applyVars χsᴿ X ⦂ R.applyTys χsᴿ Rep ] applyConceals χsᴿ c
multi-target-conceal {χsᴿ = χsᴿ} {X = X} {Rep = Rep} {c = c}
    evol c⊢ =
  subst
    (λ Σ → Σ Conv.⊢↓[
      applyVars χsᴿ X ⦂ R.applyTys χsᴿ Rep ] applyConceals χsᴿ c)
    (sym (multi-target-store evol))
    (applyConceals-⊢↓ {χs = χsᴿ} c⊢)


multi-target-reveal-position : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴿ)} {c : Conv.Conv↑ (Δᵉ Cᴿ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → (c⊢ : Σᵉ Cᴿ Conv.⊢↑[ X ⦂ Rep ] c)
  → revealGeneratorPosition (multi-target-reveal evol c⊢)
      ≡ revealGeneratorPosition c⊢
multi-target-reveal-position {χsᴿ = χsᴿ} evol c⊢ =
  trans
    (revealGeneratorPosition-store-transport
      (sym (multi-target-store evol))
      (applyReveals-⊢↑ {χs = χsᴿ} c⊢))
    (revealGeneratorPosition-apply {χs = χsᴿ} c⊢)


multi-target-conceal-position : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {X} {Rep A B : Ty (Δᵉ Cᴿ)} {c : Conv.Conv↓ (Δᵉ Cᴿ) A B}
  → (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
  → (c⊢ : Σᵉ Cᴿ Conv.⊢↓[ X ⦂ Rep ] c)
  → concealGeneratorPosition (multi-target-conceal evol c⊢)
      ≡ concealGeneratorPosition c⊢
multi-target-conceal-position {χsᴿ = χsᴿ} evol c⊢ =
  trans
    (concealGeneratorPosition-store-transport
      (sym (multi-target-store evol))
      (applyConceals-⊢↓ {χs = χsᴿ} c⊢))
    (concealGeneratorPosition-apply {χs = χsᴿ} c⊢)


multi-source-term-ctx : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Γᵉ Cᴸ′ ≡ applyTermCtxs χsᴸ (Γᵉ Cᴸ)
multi-source-term-ctx {Cᴸ = Cᴸ} evolutions-refl =
  applyTermCtxs-id (Γᵉ Cᴸ)
multi-source-term-ctx
    (evolutions-step-left {Cᴸ = Cᴸ} {χᴸ = χᴸ} {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) =
  trans (multi-source-term-ctx tail)
    (trans (cong (applyTermCtxs χsᴸ) (ctx-change-term-as eqᴸ))
      (applyTermCtxs-step χᴸ χsᴸ (Γᵉ Cᴸ)))
multi-source-term-ctx
    (evolutions-step-right eqᴿ one tail) =
  multi-source-term-ctx tail
multi-source-term-ctx
    (evolutions-step-both {Cᴸ = Cᴸ} {χᴸ = χᴸ} {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) =
  trans (multi-source-term-ctx tail)
    (trans (cong (applyTermCtxs χsᴸ) (ctx-change-term-as eqᴸ))
      (applyTermCtxs-step χᴸ χsᴸ (Γᵉ Cᴸ)))


multi-target-term-ctx : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Γᵉ Cᴿ′ ≡ applyTermCtxs χsᴿ (Γᵉ Cᴿ)
multi-target-term-ctx {Cᴿ = Cᴿ} evolutions-refl =
  applyTermCtxs-id (Γᵉ Cᴿ)
multi-target-term-ctx
    (evolutions-step-left eqᴸ one tail) =
  multi-target-term-ctx tail
multi-target-term-ctx
    (evolutions-step-right {Cᴿ = Cᴿ} {χᴿ = χᴿ} {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) =
  trans (multi-target-term-ctx tail)
    (trans (cong (applyTermCtxs χsᴿ) (ctx-change-term-as eqᴿ))
      (applyTermCtxs-step χᴿ χsᴿ (Γᵉ Cᴿ)))
multi-target-term-ctx
    (evolutions-step-both {Cᴿ = Cᴿ} {χᴿ = χᴿ} {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) =
  trans (multi-target-term-ctx tail)
    (trans (cong (applyTermCtxs χsᴿ) (ctx-change-term-as eqᴿ))
      (applyTermCtxs-step χᴿ χsᴿ (Γᵉ Cᴿ)))


ctx-change-term-value : ∀ {C C¹ : Ctx}
  → CtxChange C C¹
  → Term (Δᵉ C)
  → Term (Δᵉ C¹)
ctx-change-term-value keep-ctx M = M
ctx-change-term-value (bind-ctx eq) M = ⇑ᵗᵐ M


ctx-change-term-value-as : ∀ {C C¹ : Ctx}
    {step : CtxChange C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChange step ≡ χ
  → (M : Term (Δᵉ C))
  → ctx-change-term-value step M ≡ R.applyTerm χ M
ctx-change-term-value-as {step = keep-ctx} refl M = refl
ctx-change-term-value-as {step = bind-ctx eq} refl M = refl


multi-source-term : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Term (Δᵉ Cᴸ)
  → Term (Δᵉ Cᴸ′)
multi-source-term evolutions-refl M = M
multi-source-term
    (evolutions-step-left {stepᴸ = stepᴸ} eqᴸ one tail) M =
  multi-source-term tail (ctx-change-term-value stepᴸ M)
multi-source-term
    (evolutions-step-right eqᴿ one tail) M =
  multi-source-term tail M
multi-source-term
    (evolutions-step-both {stepᴸ = stepᴸ}
      eqᴸ eqᴿ one tail) M =
  multi-source-term tail (ctx-change-term-value stepᴸ M)


multi-target-term : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ
  → Term (Δᵉ Cᴿ)
  → Term (Δᵉ Cᴿ′)
multi-target-term evolutions-refl M = M
multi-target-term
    (evolutions-step-left eqᴸ one tail) M =
  multi-target-term tail M
multi-target-term
    (evolutions-step-right {stepᴿ = stepᴿ} eqᴿ one tail) M =
  multi-target-term tail (ctx-change-term-value stepᴿ M)
multi-target-term
    (evolutions-step-both {stepᴿ = stepᴿ}
      eqᴸ eqᴿ one tail) M =
  multi-target-term tail (ctx-change-term-value stepᴿ M)


multi-source-term-agrees : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
    (M : Term (Δᵉ Cᴸ))
  → multi-source-term evol M ≡ R.applyTerms χsᴸ M
multi-source-term-agrees evolutions-refl M = refl
multi-source-term-agrees
    (evolutions-step-left {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) M =
  trans (multi-source-term-agrees tail
          (ctx-change-term-value stepᴸ M))
    (cong (R.applyTerms χsᴸ) (ctx-change-term-value-as eqᴸ M))
multi-source-term-agrees
    (evolutions-step-right eqᴿ one tail) M =
  multi-source-term-agrees tail M
multi-source-term-agrees
    (evolutions-step-both {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) M =
  trans (multi-source-term-agrees tail
          (ctx-change-term-value stepᴸ M))
    (cong (R.applyTerms χsᴸ) (ctx-change-term-value-as eqᴸ M))


multi-target-term-agrees : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    (evol : MultiWorldEvolution {W = W} {W′ = W′} χsᴸ χsᴿ)
    (M : Term (Δᵉ Cᴿ))
  → multi-target-term evol M ≡ R.applyTerms χsᴿ M
multi-target-term-agrees evolutions-refl M = refl
multi-target-term-agrees
    (evolutions-step-left eqᴸ one tail) M =
  multi-target-term-agrees tail M
multi-target-term-agrees
    (evolutions-step-right {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) M =
  trans (multi-target-term-agrees tail
          (ctx-change-term-value stepᴿ M))
    (cong (R.applyTerms χsᴿ) (ctx-change-term-value-as eqᴿ M))
multi-target-term-agrees
    (evolutions-step-both {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) M =
  trans (multi-target-term-agrees tail
          (ctx-change-term-value stepᴿ M))
    (cong (R.applyTerms χsᴿ) (ctx-change-term-value-as eqᴿ M))
