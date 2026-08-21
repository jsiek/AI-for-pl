{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxWorldEvolutionSequenceProbe where

-- File Charter:
--   * Composes checked one-step two-Ctx world evolutions while retaining each
--     step's allocation evidence and explicit intermediate world.
--   * Keeps sequence constructors and variables in data indices; executable
--     store, context, and term transport occurs only in projection theorems.
--   * Covers unilateral scheduling as well as paired steps and checks the
--     final projections against trusted StoreChanges transport.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)

import TermCtx as TC
open import TyStore using (TyStore)
open import CastTerms using (Term; ⇑ᵗᵐ; Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
import Reduction as R
open R using (StoreChange; StoreChanges; []; _∷_)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionProbe
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionProducerProbe


data MultiWorldEvolutionᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
  → StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)
  → StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)
  → Set where

  evolutions-reflᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W} [] []

  evolutions-step-leftᶜ₀ : ∀
      {Cᴸ Cᴿ Cᴸ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W¹ : Cᴸ¹ ⊑ᶜ₀ Cᴿ}
      {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
      {χᴸ : StoreChange (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
      {stepᴸ : CtxChangeᶜ₀ Cᴸ Cᴸ¹}
    → storeChangeᶜ₀ stepᴸ ≡ χᴸ
    → WorldEvolutionᶜ₀ {W = W} {W′ = W¹} stepᴸ keep-ctxᶜ₀
    → MultiWorldEvolutionᶜ₀ {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
        (χᴸ ∷ χsᴸ) χsᴿ

  evolutions-step-rightᶜ₀ : ∀
      {Cᴸ Cᴿ Cᴿ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W¹ : Cᴸ ⊑ᶜ₀ Cᴿ¹}
      {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
      {χᴿ : StoreChange (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ′)}
      {stepᴿ : CtxChangeᶜ₀ Cᴿ Cᴿ¹}
    → storeChangeᶜ₀ stepᴿ ≡ χᴿ
    → WorldEvolutionᶜ₀ {W = W} {W′ = W¹} keep-ctxᶜ₀ stepᴿ
    → MultiWorldEvolutionᶜ₀ {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
        χsᴸ (χᴿ ∷ χsᴿ)

  evolutions-step-bothᶜ₀ : ∀
      {Cᴸ Cᴿ Cᴸ¹ Cᴿ¹ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W¹ : Cᴸ¹ ⊑ᶜ₀ Cᴿ¹}
      {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
      {χᴸ : StoreChange (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
      {χᴿ : StoreChange (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ′)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ′)}
      {stepᴸ : CtxChangeᶜ₀ Cᴸ Cᴸ¹}
      {stepᴿ : CtxChangeᶜ₀ Cᴿ Cᴿ¹}
    → storeChangeᶜ₀ stepᴸ ≡ χᴸ
    → storeChangeᶜ₀ stepᴿ ≡ χᴿ
    → WorldEvolutionᶜ₀ {W = W} {W′ = W¹} stepᴸ stepᴿ
    → MultiWorldEvolutionᶜ₀ {W = W¹} {W′ = W′} χsᴸ χsᴿ
    → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
        (χᴸ ∷ χsᴸ) (χᴿ ∷ χsᴿ)


request-source-changeᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → storeChangeᶜ₀ (evolutionSourceChangeᶜ₀ request) ≡ χᴸ
request-source-changeᶜ₀ evolution-request-keepᶜ₀ = refl
request-source-changeᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = refl
request-source-changeᶜ₀ (evolution-request-rightᶜ₀ fresh eqᴿ) = refl
request-source-changeᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = refl
request-source-changeᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = refl


request-target-changeᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → storeChangeᶜ₀ (evolutionTargetChangeᶜ₀ request) ≡ χᴿ
request-target-changeᶜ₀ evolution-request-keepᶜ₀ = refl
request-target-changeᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = refl
request-target-changeᶜ₀ (evolution-request-rightᶜ₀ fresh eqᴿ) = refl
request-target-changeᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = refl
request-target-changeᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = refl


prepend-both-requestᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹ Δᴿ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ¹ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ¹ (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀
      {W = evolutionWorldᶜ₀ request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
      (χᴸ ∷ χsᴸ) (χᴿ ∷ χsᴿ)
prepend-both-requestᶜ₀ request tail =
  evolutions-step-bothᶜ₀
    (request-source-changeᶜ₀ request)
    (request-target-changeᶜ₀ request)
    (produceWorldEvolutionᶜ₀ request) tail


prepend-left-requestᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ¹} {χᴸ : StoreChange Δᴸ Δᴸ¹}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ R.keep)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ¹ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀
      {W = evolutionWorldᶜ₀ request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
      (χᴸ ∷ χsᴸ) χsᴿ
prepend-left-requestᶜ₀ evolution-request-keepᶜ₀ tail =
  evolutions-step-leftᶜ₀ refl evolution-keepᶜ₀ tail
prepend-left-requestᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) tail =
  evolutions-step-leftᶜ₀ refl (evolution-bind-leftᶜ₀ eqᴸ) tail


prepend-right-requestᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴿ¹} {χᴿ : StoreChange Δᴿ Δᴿ¹}
    (request : WorldEvolutionRequestᶜ₀ W R.keep χᴿ)
    {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges Δᴸ (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges Δᴿ¹ (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀
      {W = evolutionWorldᶜ₀ request} {W′ = W′} χsᴸ χsᴿ
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′}
      χsᴸ (χᴿ ∷ χsᴿ)
prepend-right-requestᶜ₀ evolution-request-keepᶜ₀ tail =
  evolutions-step-rightᶜ₀ refl evolution-keepᶜ₀ tail
prepend-right-requestᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) tail =
  evolutions-step-rightᶜ₀ refl
    (evolution-bind-rightᶜ₀ fresh eqᴿ) tail


ctx-change-store-asᶜ₀ : ∀ {C C¹ : Ctx}
    {step : CtxChangeᶜ₀ C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChangeᶜ₀ step ≡ χ
  → Σᵉ C¹ ≡ R.applyStore χ (Σᵉ C)
ctx-change-store-asᶜ₀ {C = C} {step = step} eq =
  trans (ctx-change-storeᶜ₀ step)
    (cong (λ ψ → R.applyStore ψ (Σᵉ C)) eq)


ctx-change-term-asᶜ₀ : ∀ {C C¹ : Ctx}
    {step : CtxChangeᶜ₀ C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChangeᶜ₀ step ≡ χ
  → Γᵉ C¹ ≡ applyTermCtxᶜ₀ χ (Γᵉ C)
ctx-change-term-asᶜ₀ {C = C} {step = step} eq =
  trans (ctx-change-termᶜ₀ step)
    (cong (λ ψ → applyTermCtxᶜ₀ ψ (Γᵉ C)) eq)


multi-source-storeᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Σᵉ Cᴸ′ ≡ R.applyStores χsᴸ (Σᵉ Cᴸ)
multi-source-storeᶜ₀ evolutions-reflᶜ₀ = refl
multi-source-storeᶜ₀
    (evolutions-step-leftᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) =
  trans (multi-source-storeᶜ₀ tail)
    (cong (R.applyStores χsᴸ) (ctx-change-store-asᶜ₀ eqᴸ))
multi-source-storeᶜ₀
    (evolutions-step-rightᶜ₀ eqᴿ one tail) =
  multi-source-storeᶜ₀ tail
multi-source-storeᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) =
  trans (multi-source-storeᶜ₀ tail)
    (cong (R.applyStores χsᴸ) (ctx-change-store-asᶜ₀ eqᴸ))


multi-target-storeᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Σᵉ Cᴿ′ ≡ R.applyStores χsᴿ (Σᵉ Cᴿ)
multi-target-storeᶜ₀ evolutions-reflᶜ₀ = refl
multi-target-storeᶜ₀
    (evolutions-step-leftᶜ₀ eqᴸ one tail) =
  multi-target-storeᶜ₀ tail
multi-target-storeᶜ₀
    (evolutions-step-rightᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) =
  trans (multi-target-storeᶜ₀ tail)
    (cong (R.applyStores χsᴿ) (ctx-change-store-asᶜ₀ eqᴿ))
multi-target-storeᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) =
  trans (multi-target-storeᶜ₀ tail)
    (cong (R.applyStores χsᴿ) (ctx-change-store-asᶜ₀ eqᴿ))


applyTermCtxsᶜ₀ : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → TC.TermCtx Δ
  → TC.TermCtx Δ′
applyTermCtxsᶜ₀ [] Γ = Γ
applyTermCtxsᶜ₀ (χ ∷ χs) Γ =
  applyTermCtxsᶜ₀ χs (applyTermCtxᶜ₀ χ Γ)


multi-source-term-ctxᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Γᵉ Cᴸ′ ≡ applyTermCtxsᶜ₀ χsᴸ (Γᵉ Cᴸ)
multi-source-term-ctxᶜ₀ evolutions-reflᶜ₀ = refl
multi-source-term-ctxᶜ₀
    (evolutions-step-leftᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) =
  trans (multi-source-term-ctxᶜ₀ tail)
    (cong (applyTermCtxsᶜ₀ χsᴸ) (ctx-change-term-asᶜ₀ eqᴸ))
multi-source-term-ctxᶜ₀
    (evolutions-step-rightᶜ₀ eqᴿ one tail) =
  multi-source-term-ctxᶜ₀ tail
multi-source-term-ctxᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) =
  trans (multi-source-term-ctxᶜ₀ tail)
    (cong (applyTermCtxsᶜ₀ χsᴸ) (ctx-change-term-asᶜ₀ eqᴸ))


multi-target-term-ctxᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Γᵉ Cᴿ′ ≡ applyTermCtxsᶜ₀ χsᴿ (Γᵉ Cᴿ)
multi-target-term-ctxᶜ₀ evolutions-reflᶜ₀ = refl
multi-target-term-ctxᶜ₀
    (evolutions-step-leftᶜ₀ eqᴸ one tail) =
  multi-target-term-ctxᶜ₀ tail
multi-target-term-ctxᶜ₀
    (evolutions-step-rightᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) =
  trans (multi-target-term-ctxᶜ₀ tail)
    (cong (applyTermCtxsᶜ₀ χsᴿ) (ctx-change-term-asᶜ₀ eqᴿ))
multi-target-term-ctxᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) =
  trans (multi-target-term-ctxᶜ₀ tail)
    (cong (applyTermCtxsᶜ₀ χsᴿ) (ctx-change-term-asᶜ₀ eqᴿ))


ctx-change-term-valueᶜ₀ : ∀ {C C¹ : Ctx}
  → CtxChangeᶜ₀ C C¹
  → Term (Δᵉ C)
  → Term (Δᵉ C¹)
ctx-change-term-valueᶜ₀ keep-ctxᶜ₀ M = M
ctx-change-term-valueᶜ₀ (bind-ctxᶜ₀ eq) M = ⇑ᵗᵐ M


ctx-change-term-value-asᶜ₀ : ∀ {C C¹ : Ctx}
    {step : CtxChangeᶜ₀ C C¹}
    {χ : StoreChange (Δᵉ C) (Δᵉ C¹)}
  → storeChangeᶜ₀ step ≡ χ
  → (M : Term (Δᵉ C))
  → ctx-change-term-valueᶜ₀ step M ≡ R.applyTerm χ M
ctx-change-term-value-asᶜ₀ {step = keep-ctxᶜ₀} refl M = refl
ctx-change-term-value-asᶜ₀ {step = bind-ctxᶜ₀ eq} refl M = refl


multi-source-termᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Term (Δᵉ Cᴸ)
  → Term (Δᵉ Cᴸ′)
multi-source-termᶜ₀ evolutions-reflᶜ₀ M = M
multi-source-termᶜ₀
    (evolutions-step-leftᶜ₀ {stepᴸ = stepᴸ} eqᴸ one tail) M =
  multi-source-termᶜ₀ tail (ctx-change-term-valueᶜ₀ stepᴸ M)
multi-source-termᶜ₀
    (evolutions-step-rightᶜ₀ eqᴿ one tail) M =
  multi-source-termᶜ₀ tail M
multi-source-termᶜ₀
    (evolutions-step-bothᶜ₀ {stepᴸ = stepᴸ}
      eqᴸ eqᴿ one tail) M =
  multi-source-termᶜ₀ tail (ctx-change-term-valueᶜ₀ stepᴸ M)


multi-target-termᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ
  → Term (Δᵉ Cᴿ)
  → Term (Δᵉ Cᴿ′)
multi-target-termᶜ₀ evolutions-reflᶜ₀ M = M
multi-target-termᶜ₀
    (evolutions-step-leftᶜ₀ eqᴸ one tail) M =
  multi-target-termᶜ₀ tail M
multi-target-termᶜ₀
    (evolutions-step-rightᶜ₀ {stepᴿ = stepᴿ} eqᴿ one tail) M =
  multi-target-termᶜ₀ tail (ctx-change-term-valueᶜ₀ stepᴿ M)
multi-target-termᶜ₀
    (evolutions-step-bothᶜ₀ {stepᴿ = stepᴿ}
      eqᴸ eqᴿ one tail) M =
  multi-target-termᶜ₀ tail (ctx-change-term-valueᶜ₀ stepᴿ M)


multi-source-term-agreesᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    (evol : MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ)
    (M : Term (Δᵉ Cᴸ))
  → multi-source-termᶜ₀ evol M ≡ R.applyTerms χsᴸ M
multi-source-term-agreesᶜ₀ evolutions-reflᶜ₀ M = refl
multi-source-term-agreesᶜ₀
    (evolutions-step-leftᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ one tail) M =
  trans (multi-source-term-agreesᶜ₀ tail
          (ctx-change-term-valueᶜ₀ stepᴸ M))
    (cong (R.applyTerms χsᴸ) (ctx-change-term-value-asᶜ₀ eqᴸ M))
multi-source-term-agreesᶜ₀
    (evolutions-step-rightᶜ₀ eqᴿ one tail) M =
  multi-source-term-agreesᶜ₀ tail M
multi-source-term-agreesᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴸ = χsᴸ}
      {stepᴸ = stepᴸ} eqᴸ eqᴿ one tail) M =
  trans (multi-source-term-agreesᶜ₀ tail
          (ctx-change-term-valueᶜ₀ stepᴸ M))
    (cong (R.applyTerms χsᴸ) (ctx-change-term-value-asᶜ₀ eqᴸ M))


multi-target-term-agreesᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    (evol : MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ)
    (M : Term (Δᵉ Cᴿ))
  → multi-target-termᶜ₀ evol M ≡ R.applyTerms χsᴿ M
multi-target-term-agreesᶜ₀ evolutions-reflᶜ₀ M = refl
multi-target-term-agreesᶜ₀
    (evolutions-step-leftᶜ₀ eqᴸ one tail) M =
  multi-target-term-agreesᶜ₀ tail M
multi-target-term-agreesᶜ₀
    (evolutions-step-rightᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴿ one tail) M =
  trans (multi-target-term-agreesᶜ₀ tail
          (ctx-change-term-valueᶜ₀ stepᴿ M))
    (cong (R.applyTerms χsᴿ) (ctx-change-term-value-asᶜ₀ eqᴿ M))
multi-target-term-agreesᶜ₀
    (evolutions-step-bothᶜ₀ {χsᴿ = χsᴿ}
      {stepᴿ = stepᴿ} eqᴸ eqᴿ one tail) M =
  trans (multi-target-term-agreesᶜ₀ tail
          (ctx-change-term-valueᶜ₀ stepᴿ M))
    (cong (R.applyTerms χsᴿ) (ctx-change-term-value-asᶜ₀ eqᴿ M))
