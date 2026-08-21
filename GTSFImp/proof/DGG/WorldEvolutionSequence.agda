{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolutionSequence where

-- File Charter:
--   * Composes one-step two-Ctx world evolutions while retaining each
--     step's allocation evidence and explicit intermediate world.
--   * Keeps sequence constructors and variables in data indices; executable
--     store, context, and term transport occurs only in projection theorems.
--   * Covers unilateral scheduling as well as paired steps and checks the
--     final projections against trusted StoreChanges transport.
--   * Exports MultiWorldEvolution, request prepend operations, and final
--     store/context/term projections; depends on one-step evolution, its
--     request producer, and the preservation context action.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)

import TermCtx as TC
open import TyStore using (TyStore)
open import CastTerms using (Term; ⇑ᵗᵐ; Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
import Reduction as R
open R using (StoreChange; StoreChanges; []; _∷_)
open import proof.TypeSafety.Preservation using
  (applyTermCtx; applyTermCtxs; applyTermCtxs-id; applyTermCtxs-step)
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
