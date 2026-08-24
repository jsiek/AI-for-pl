{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolutionProducer where

-- File Charter:
--   * Defines the operational producer contract for one-step two-Ctx world
--     evolution from a pair of trusted StoreChange results.
--   * Keeps StoreChange constructors, rather than apply functions, in data
--     indices and records exactly the evidence required by each allocation.
--   * Computes endpoint contexts and the evolved world, then proves that its
--     store and term-context projections agree with trusted transport.
--   * Exports WorldEvolutionRequest and produceWorldEvolution; depends on the
--     constructor-form two-Ctx world and one-step evolution modules.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; ★; ⇑ᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Term; ⇑ᵗᵐ; Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.TypeSafety.Preservation using (applyTermCtx)
open import proof.DGG.World
open import proof.DGG.WorldEvolution


data WorldEvolutionRequest :
    ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
    → ∀ {Δᴸ′ Δᴿ′}
    → R.StoreChange Δᴸ Δᴸ′
    → R.StoreChange Δᴿ Δᴿ′
    → Set where

  evolution-request-keep : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → WorldEvolutionRequest W R.keep R.keep

  evolution-request-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
    → WorldEvolutionRequest W (R.bind A) R.keep

  evolution-request-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → RightBindFreshᶜ W B
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → WorldEvolutionRequest W R.keep (R.bind B)

  evolution-request-both-precise : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → A ⊑ᵀ⟨ W ⟩ B
    → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → WorldEvolutionRequest W (R.bind A) (R.bind B)

  evolution-request-both-dynamic : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → A ⊑ᵀ⟨ W ⟩ B
    → ⇑ᵗ A ≢ ★
    → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → WorldEvolutionRequest W (R.bind A) (R.bind B)


evolutionSourceStoreValue : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → TyStore Δᴸ′
evolutionSourceStoreValue {Σᴸ = Σᴸ}
    evolution-request-keep = Σᴸ
evolutionSourceStoreValue {Σᴸ = Σᴸ}
    (evolution-request-left {A = A} eqᴸ) = store-bind Σᴸ A
evolutionSourceStoreValue {Σᴸ = Σᴸ}
    (evolution-request-right fresh eqᴿ) = Σᴸ
evolutionSourceStoreValue {Σᴸ = Σᴸ}
    (evolution-request-both-precise
      {A = A} represented eqᴸ eqᴿ) = store-bind Σᴸ A
evolutionSourceStoreValue {Σᴸ = Σᴸ}
    (evolution-request-both-dynamic
      {A = A} represented A≠★ eqᴸ eqᴿ) = store-bind Σᴸ A


evolutionSourceTermCtxValue : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → TermCtx Δᴸ′
evolutionSourceTermCtxValue {Γᴸ = Γᴸ}
    evolution-request-keep = Γᴸ
evolutionSourceTermCtxValue
    (evolution-request-left {Γᴸ⁺ = Γᴸ⁺} eqᴸ) = Γᴸ⁺
evolutionSourceTermCtxValue {Γᴸ = Γᴸ}
    (evolution-request-right fresh eqᴿ) = Γᴸ
evolutionSourceTermCtxValue
    (evolution-request-both-precise
      {Γᴸ⁺ = Γᴸ⁺} represented eqᴸ eqᴿ) = Γᴸ⁺
evolutionSourceTermCtxValue
    (evolution-request-both-dynamic
      {Γᴸ⁺ = Γᴸ⁺} represented A≠★ eqᴸ eqᴿ) = Γᴸ⁺


evolutionTargetStoreValue : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → TyStore Δᴿ′
evolutionTargetStoreValue {Σᴿ = Σᴿ}
    evolution-request-keep = Σᴿ
evolutionTargetStoreValue {Σᴿ = Σᴿ}
    (evolution-request-left eqᴸ) = Σᴿ
evolutionTargetStoreValue {Σᴿ = Σᴿ}
    (evolution-request-right
      {B = B} fresh eqᴿ) = store-bind Σᴿ B
evolutionTargetStoreValue {Σᴿ = Σᴿ}
    (evolution-request-both-precise
      {B = B} represented eqᴸ eqᴿ) = store-bind Σᴿ B
evolutionTargetStoreValue {Σᴿ = Σᴿ}
    (evolution-request-both-dynamic
      {B = B} represented A≠★ eqᴸ eqᴿ) = store-bind Σᴿ B


evolutionTargetTermCtxValue : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → TermCtx Δᴿ′
evolutionTargetTermCtxValue {Γᴿ = Γᴿ}
    evolution-request-keep = Γᴿ
evolutionTargetTermCtxValue {Γᴿ = Γᴿ}
    (evolution-request-left eqᴸ) = Γᴿ
evolutionTargetTermCtxValue
    (evolution-request-right {Γᴿ⁺ = Γᴿ⁺} fresh eqᴿ) = Γᴿ⁺
evolutionTargetTermCtxValue
    (evolution-request-both-precise
      {Γᴿ⁺ = Γᴿ⁺} represented eqᴸ eqᴿ) = Γᴿ⁺
evolutionTargetTermCtxValue
    (evolution-request-both-dynamic
      {Γᴿ⁺ = Γᴿ⁺} represented A≠★ eqᴸ eqᴿ) = Γᴿ⁺


evolutionSourceCtx : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → Ctx
evolutionSourceCtx {Δᴸ′ = Δᴸ′} request =
  ⟨ Δᴸ′ , evolutionSourceStoreValue request
  , evolutionSourceTermCtxValue request ⟩


evolutionTargetCtx : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → Ctx
evolutionTargetCtx {Δᴿ′ = Δᴿ′} request =
  ⟨ Δᴿ′ , evolutionTargetStoreValue request
  , evolutionTargetTermCtxValue request ⟩


evolutionSourceTerm : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → Term Δᴸ
  → Term Δᴸ′
evolutionSourceTerm evolution-request-keep M = M
evolutionSourceTerm (evolution-request-left eqᴸ) M =
  ⇑ᵗᵐ M
evolutionSourceTerm (evolution-request-right fresh eqᴿ) M = M
evolutionSourceTerm
    (evolution-request-both-precise represented eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M
evolutionSourceTerm
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M


evolutionTargetTerm : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequest W χᴸ χᴿ
  → Term Δᴿ
  → Term Δᴿ′
evolutionTargetTerm evolution-request-keep M = M
evolutionTargetTerm (evolution-request-left eqᴸ) M = M
evolutionTargetTerm (evolution-request-right fresh eqᴿ) M =
  ⇑ᵗᵐ M
evolutionTargetTerm
    (evolution-request-both-precise represented eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M
evolutionTargetTerm
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M


evolutionWorld : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequest W χᴸ χᴿ)
  → evolutionSourceCtx request ⊑ᶜ evolutionTargetCtx request
evolutionWorld {W = W} evolution-request-keep = W
evolutionWorld {W = W} (evolution-request-left {A = A} eqᴸ) =
  W ▻ᶜ bind-left-changeᶜ A eqᴸ
evolutionWorld {W = W}
    (evolution-request-right {B = B} fresh eqᴿ) =
  W ▻ᶜ bind-right-changeᶜ B fresh eqᴿ
evolutionWorld {W = W}
    (evolution-request-both-precise represented eqᴸ eqᴿ) =
  W ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ
evolutionWorld {W = W}
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) =
  W ▻ᶜ bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ


evolutionSourceStore : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → Σᵉ (evolutionSourceCtx request) ≡ R.applyStore χᴸ Σᴸ
evolutionSourceStore evolution-request-keep = refl
evolutionSourceStore (evolution-request-left eqᴸ) = refl
evolutionSourceStore
    (evolution-request-right fresh eqᴿ) = refl
evolutionSourceStore
    (evolution-request-both-precise represented eqᴸ eqᴿ) = refl
evolutionSourceStore
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = refl


evolutionTargetStore : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → Σᵉ (evolutionTargetCtx request) ≡ R.applyStore χᴿ Σᴿ
evolutionTargetStore evolution-request-keep = refl
evolutionTargetStore (evolution-request-left eqᴸ) = refl
evolutionTargetStore
    (evolution-request-right fresh eqᴿ) = refl
evolutionTargetStore
    (evolution-request-both-precise represented eqᴸ eqᴿ) = refl
evolutionTargetStore
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = refl


evolutionSourceTerm-agrees : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
    (M : Term Δᴸ)
  → evolutionSourceTerm request M ≡ R.applyTerm χᴸ M
evolutionSourceTerm-agrees evolution-request-keep M = refl
evolutionSourceTerm-agrees
    (evolution-request-left eqᴸ) M = refl
evolutionSourceTerm-agrees
    (evolution-request-right fresh eqᴿ) M = refl
evolutionSourceTerm-agrees
    (evolution-request-both-precise represented eqᴸ eqᴿ) M = refl
evolutionSourceTerm-agrees
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) M = refl


evolutionTargetTerm-agrees : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
    (M : Term Δᴿ)
  → evolutionTargetTerm request M ≡ R.applyTerm χᴿ M
evolutionTargetTerm-agrees evolution-request-keep M = refl
evolutionTargetTerm-agrees
    (evolution-request-left eqᴸ) M = refl
evolutionTargetTerm-agrees
    (evolution-request-right fresh eqᴿ) M = refl
evolutionTargetTerm-agrees
    (evolution-request-both-precise represented eqᴸ eqᴿ) M = refl
evolutionTargetTerm-agrees
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) M = refl


evolutionSourceTermCtx : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → Γᵉ (evolutionSourceCtx request)
    ≡ applyTermCtx χᴸ Γᴸ
evolutionSourceTermCtx evolution-request-keep = refl
evolutionSourceTermCtx (evolution-request-left eqᴸ) = eqᴸ
evolutionSourceTermCtx
    (evolution-request-right fresh eqᴿ) = refl
evolutionSourceTermCtx
    (evolution-request-both-precise represented eqᴸ eqᴿ) = eqᴸ
evolutionSourceTermCtx
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = eqᴸ


evolutionTargetTermCtx : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → Γᵉ (evolutionTargetCtx request)
    ≡ applyTermCtx χᴿ Γᴿ
evolutionTargetTermCtx evolution-request-keep = refl
evolutionTargetTermCtx (evolution-request-left eqᴸ) = refl
evolutionTargetTermCtx
    (evolution-request-right fresh eqᴿ) = eqᴿ
evolutionTargetTermCtx
    (evolution-request-both-precise represented eqᴸ eqᴿ) = eqᴿ
evolutionTargetTermCtx
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) = eqᴿ


evolutionSourceChange : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequest W χᴸ χᴿ)
  → CtxChange ⟨ Δᴸ , Σᴸ , Γᴸ ⟩
      (evolutionSourceCtx request)
evolutionSourceChange evolution-request-keep = keep-ctx
evolutionSourceChange (evolution-request-left eqᴸ) =
  bind-ctx eqᴸ
evolutionSourceChange
    (evolution-request-right fresh eqᴿ) = keep-ctx
evolutionSourceChange
    (evolution-request-both-precise represented eqᴸ eqᴿ) =
  bind-ctx eqᴸ
evolutionSourceChange
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) =
  bind-ctx eqᴸ


evolutionTargetChange : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequest W χᴸ χᴿ)
  → CtxChange ⟨ Δᴿ , Σᴿ , Γᴿ ⟩
      (evolutionTargetCtx request)
evolutionTargetChange evolution-request-keep = keep-ctx
evolutionTargetChange (evolution-request-left eqᴸ) = keep-ctx
evolutionTargetChange
    (evolution-request-right fresh eqᴿ) = bind-ctx eqᴿ
evolutionTargetChange
    (evolution-request-both-precise represented eqᴸ eqᴿ) =
  bind-ctx eqᴿ
evolutionTargetChange
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) =
  bind-ctx eqᴿ


produceWorldEvolution : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequest W χᴸ χᴿ)
  → WorldEvolution
      {W = W} {W′ = evolutionWorld request}
      (evolutionSourceChange request)
      (evolutionTargetChange request)
produceWorldEvolution evolution-request-keep = evolution-keep
produceWorldEvolution (evolution-request-left eqᴸ) =
  evolution-bind-left eqᴸ
produceWorldEvolution
    (evolution-request-right fresh eqᴿ) =
  evolution-bind-right fresh eqᴿ
produceWorldEvolution
    (evolution-request-both-precise represented eqᴸ eqᴿ) =
  evolution-bind-both represented eqᴸ eqᴿ
produceWorldEvolution
    (evolution-request-both-dynamic
      represented A≠★ eqᴸ eqᴿ) =
  evolution-bind-both-star represented A≠★ eqᴸ eqᴿ


-- `StoreChange` exposes only `keep` or `bind A`.  It does not expose the
-- right-only freshness proof, the paired allocation's `A ⊑ᵀ⟨ W ⟩ B`, or
-- the precise/dynamic choice and its `⇑ᵗ A ≢ ★` evidence.  These are the
-- exact extra facts the reduction/simulation producer must retain.  A bare
-- reduction step also carries no term contexts; a typed producer must supply
-- the displayed shift equalities (canonically `refl` when it builds them).
