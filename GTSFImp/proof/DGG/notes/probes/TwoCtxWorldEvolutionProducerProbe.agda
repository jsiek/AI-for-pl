{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxWorldEvolutionProducerProbe where

-- File Charter:
--   * Checks the operational producer contract for one-step two-Ctx world
--     evolution from a pair of trusted StoreChange results.
--   * Keeps StoreChange constructors, rather than apply functions, in data
--     indices and records exactly the evidence required by each allocation.
--   * Computes endpoint contexts and the evolved world, then proves that its
--     store and term-context projections agree with trusted transport.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; ★; ⇑ᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Term; ⇑ᵗᵐ; Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.DGG.TwoCtxWorld
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionProbe


data WorldEvolutionRequestᶜ₀ :
    ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
    → ∀ {Δᴸ′ Δᴿ′}
    → R.StoreChange Δᴸ Δᴸ′
    → R.StoreChange Δᴿ Δᴿ′
    → Set where

  evolution-request-keepᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → WorldEvolutionRequestᶜ₀ W R.keep R.keep

  evolution-request-leftᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
    → WorldEvolutionRequestᶜ₀ W (R.bind A) R.keep

  evolution-request-rightᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → RightBindFreshᶜ W B
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → WorldEvolutionRequestᶜ₀ W R.keep (R.bind B)

  evolution-request-both-preciseᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → A ⊑ᵀ⟨ W ⟩ B
    → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → WorldEvolutionRequestᶜ₀ W (R.bind A) (R.bind B)

  evolution-request-both-dynamicᶜ₀ : ∀
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
    → WorldEvolutionRequestᶜ₀ W (R.bind A) (R.bind B)


evolutionSourceStoreValueᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → TyStore Δᴸ′
evolutionSourceStoreValueᶜ₀ {Σᴸ = Σᴸ}
    evolution-request-keepᶜ₀ = Σᴸ
evolutionSourceStoreValueᶜ₀ {Σᴸ = Σᴸ}
    (evolution-request-leftᶜ₀ {A = A} eqᴸ) = store-bind Σᴸ A
evolutionSourceStoreValueᶜ₀ {Σᴸ = Σᴸ}
    (evolution-request-rightᶜ₀ fresh eqᴿ) = Σᴸ
evolutionSourceStoreValueᶜ₀ {Σᴸ = Σᴸ}
    (evolution-request-both-preciseᶜ₀
      {A = A} represented eqᴸ eqᴿ) = store-bind Σᴸ A
evolutionSourceStoreValueᶜ₀ {Σᴸ = Σᴸ}
    (evolution-request-both-dynamicᶜ₀
      {A = A} represented A≠★ eqᴸ eqᴿ) = store-bind Σᴸ A


evolutionSourceTermCtxValueᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → TermCtx Δᴸ′
evolutionSourceTermCtxValueᶜ₀ {Γᴸ = Γᴸ}
    evolution-request-keepᶜ₀ = Γᴸ
evolutionSourceTermCtxValueᶜ₀
    (evolution-request-leftᶜ₀ {Γᴸ⁺ = Γᴸ⁺} eqᴸ) = Γᴸ⁺
evolutionSourceTermCtxValueᶜ₀ {Γᴸ = Γᴸ}
    (evolution-request-rightᶜ₀ fresh eqᴿ) = Γᴸ
evolutionSourceTermCtxValueᶜ₀
    (evolution-request-both-preciseᶜ₀
      {Γᴸ⁺ = Γᴸ⁺} represented eqᴸ eqᴿ) = Γᴸ⁺
evolutionSourceTermCtxValueᶜ₀
    (evolution-request-both-dynamicᶜ₀
      {Γᴸ⁺ = Γᴸ⁺} represented A≠★ eqᴸ eqᴿ) = Γᴸ⁺


evolutionTargetStoreValueᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → TyStore Δᴿ′
evolutionTargetStoreValueᶜ₀ {Σᴿ = Σᴿ}
    evolution-request-keepᶜ₀ = Σᴿ
evolutionTargetStoreValueᶜ₀ {Σᴿ = Σᴿ}
    (evolution-request-leftᶜ₀ eqᴸ) = Σᴿ
evolutionTargetStoreValueᶜ₀ {Σᴿ = Σᴿ}
    (evolution-request-rightᶜ₀
      {B = B} fresh eqᴿ) = store-bind Σᴿ B
evolutionTargetStoreValueᶜ₀ {Σᴿ = Σᴿ}
    (evolution-request-both-preciseᶜ₀
      {B = B} represented eqᴸ eqᴿ) = store-bind Σᴿ B
evolutionTargetStoreValueᶜ₀ {Σᴿ = Σᴿ}
    (evolution-request-both-dynamicᶜ₀
      {B = B} represented A≠★ eqᴸ eqᴿ) = store-bind Σᴿ B


evolutionTargetTermCtxValueᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → TermCtx Δᴿ′
evolutionTargetTermCtxValueᶜ₀ {Γᴿ = Γᴿ}
    evolution-request-keepᶜ₀ = Γᴿ
evolutionTargetTermCtxValueᶜ₀ {Γᴿ = Γᴿ}
    (evolution-request-leftᶜ₀ eqᴸ) = Γᴿ
evolutionTargetTermCtxValueᶜ₀
    (evolution-request-rightᶜ₀ {Γᴿ⁺ = Γᴿ⁺} fresh eqᴿ) = Γᴿ⁺
evolutionTargetTermCtxValueᶜ₀
    (evolution-request-both-preciseᶜ₀
      {Γᴿ⁺ = Γᴿ⁺} represented eqᴸ eqᴿ) = Γᴿ⁺
evolutionTargetTermCtxValueᶜ₀
    (evolution-request-both-dynamicᶜ₀
      {Γᴿ⁺ = Γᴿ⁺} represented A≠★ eqᴸ eqᴿ) = Γᴿ⁺


evolutionSourceCtxᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → Ctx
evolutionSourceCtxᶜ₀ {Δᴸ′ = Δᴸ′} request =
  ⟨ Δᴸ′ , evolutionSourceStoreValueᶜ₀ request
  , evolutionSourceTermCtxValueᶜ₀ request ⟩


evolutionTargetCtxᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → Ctx
evolutionTargetCtxᶜ₀ {Δᴿ′ = Δᴿ′} request =
  ⟨ Δᴿ′ , evolutionTargetStoreValueᶜ₀ request
  , evolutionTargetTermCtxValueᶜ₀ request ⟩


evolutionSourceTermᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → Term Δᴸ
  → Term Δᴸ′
evolutionSourceTermᶜ₀ evolution-request-keepᶜ₀ M = M
evolutionSourceTermᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) M =
  ⇑ᵗᵐ M
evolutionSourceTermᶜ₀ (evolution-request-rightᶜ₀ fresh eqᴿ) M = M
evolutionSourceTermᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M
evolutionSourceTermᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M


evolutionTargetTermᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → WorldEvolutionRequestᶜ₀ W χᴸ χᴿ
  → Term Δᴿ
  → Term Δᴿ′
evolutionTargetTermᶜ₀ evolution-request-keepᶜ₀ M = M
evolutionTargetTermᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) M = M
evolutionTargetTermᶜ₀ (evolution-request-rightᶜ₀ fresh eqᴿ) M =
  ⇑ᵗᵐ M
evolutionTargetTermᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M
evolutionTargetTermᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) M =
  ⇑ᵗᵐ M


evolutionWorldᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → evolutionSourceCtxᶜ₀ request ⊑ᶜ evolutionTargetCtxᶜ₀ request
evolutionWorldᶜ₀ {W = W} evolution-request-keepᶜ₀ = W
evolutionWorldᶜ₀ {W = W} (evolution-request-leftᶜ₀ {A = A} eqᴸ) =
  bind-left-rawᶜ W A eqᴸ
evolutionWorldᶜ₀ {W = W}
    (evolution-request-rightᶜ₀ {B = B} fresh eqᴿ) =
  bind-right-rawᶜ W B fresh eqᴿ
evolutionWorldᶜ₀ {W = W}
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) =
  bind-both-rawᶜ W represented eqᴸ eqᴿ
evolutionWorldᶜ₀ {W = W}
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) =
  bind-both-star-rawᶜ W represented A≠★ eqᴸ eqᴿ


evolutionSourceStoreᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → Σᵉ (evolutionSourceCtxᶜ₀ request) ≡ R.applyStore χᴸ Σᴸ
evolutionSourceStoreᶜ₀ evolution-request-keepᶜ₀ = refl
evolutionSourceStoreᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = refl
evolutionSourceStoreᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = refl
evolutionSourceStoreᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = refl
evolutionSourceStoreᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = refl


evolutionTargetStoreᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → Σᵉ (evolutionTargetCtxᶜ₀ request) ≡ R.applyStore χᴿ Σᴿ
evolutionTargetStoreᶜ₀ evolution-request-keepᶜ₀ = refl
evolutionTargetStoreᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = refl
evolutionTargetStoreᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = refl
evolutionTargetStoreᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = refl
evolutionTargetStoreᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = refl


evolutionSourceTerm-agreesᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
    (M : Term Δᴸ)
  → evolutionSourceTermᶜ₀ request M ≡ R.applyTerm χᴸ M
evolutionSourceTerm-agreesᶜ₀ evolution-request-keepᶜ₀ M = refl
evolutionSourceTerm-agreesᶜ₀
    (evolution-request-leftᶜ₀ eqᴸ) M = refl
evolutionSourceTerm-agreesᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) M = refl
evolutionSourceTerm-agreesᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) M = refl
evolutionSourceTerm-agreesᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) M = refl


evolutionTargetTerm-agreesᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
    (M : Term Δᴿ)
  → evolutionTargetTermᶜ₀ request M ≡ R.applyTerm χᴿ M
evolutionTargetTerm-agreesᶜ₀ evolution-request-keepᶜ₀ M = refl
evolutionTargetTerm-agreesᶜ₀
    (evolution-request-leftᶜ₀ eqᴸ) M = refl
evolutionTargetTerm-agreesᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) M = refl
evolutionTargetTerm-agreesᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) M = refl
evolutionTargetTerm-agreesᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) M = refl


evolutionSourceTermCtxᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → Γᵉ (evolutionSourceCtxᶜ₀ request)
    ≡ applyTermCtxᶜ₀ χᴸ Γᴸ
evolutionSourceTermCtxᶜ₀ evolution-request-keepᶜ₀ = refl
evolutionSourceTermCtxᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = eqᴸ
evolutionSourceTermCtxᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = refl
evolutionSourceTermCtxᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = eqᴸ
evolutionSourceTermCtxᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = eqᴸ


evolutionTargetTermCtxᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → Γᵉ (evolutionTargetCtxᶜ₀ request)
    ≡ applyTermCtxᶜ₀ χᴿ Γᴿ
evolutionTargetTermCtxᶜ₀ evolution-request-keepᶜ₀ = refl
evolutionTargetTermCtxᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = refl
evolutionTargetTermCtxᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = eqᴿ
evolutionTargetTermCtxᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) = eqᴿ
evolutionTargetTermCtxᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) = eqᴿ


evolutionSourceChangeᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → CtxChangeᶜ₀ ⟨ Δᴸ , Σᴸ , Γᴸ ⟩
      (evolutionSourceCtxᶜ₀ request)
evolutionSourceChangeᶜ₀ evolution-request-keepᶜ₀ = keep-ctxᶜ₀
evolutionSourceChangeᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) =
  bind-ctxᶜ₀ eqᴸ
evolutionSourceChangeᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = keep-ctxᶜ₀
evolutionSourceChangeᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) =
  bind-ctxᶜ₀ eqᴸ
evolutionSourceChangeᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) =
  bind-ctxᶜ₀ eqᴸ


evolutionTargetChangeᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
  → (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → CtxChangeᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩
      (evolutionTargetCtxᶜ₀ request)
evolutionTargetChangeᶜ₀ evolution-request-keepᶜ₀ = keep-ctxᶜ₀
evolutionTargetChangeᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) = keep-ctxᶜ₀
evolutionTargetChangeᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) = bind-ctxᶜ₀ eqᴿ
evolutionTargetChangeᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) =
  bind-ctxᶜ₀ eqᴿ
evolutionTargetChangeᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) =
  bind-ctxᶜ₀ eqᴿ


produceWorldEvolutionᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Δᴸ′ Δᴿ′} {χᴸ : R.StoreChange Δᴸ Δᴸ′}
    {χᴿ : R.StoreChange Δᴿ Δᴿ′}
    (request : WorldEvolutionRequestᶜ₀ W χᴸ χᴿ)
  → WorldEvolutionᶜ₀
      {W = W} {W′ = evolutionWorldᶜ₀ request}
      (evolutionSourceChangeᶜ₀ request)
      (evolutionTargetChangeᶜ₀ request)
produceWorldEvolutionᶜ₀ evolution-request-keepᶜ₀ = evolution-keepᶜ₀
produceWorldEvolutionᶜ₀ (evolution-request-leftᶜ₀ eqᴸ) =
  evolution-bind-leftᶜ₀ eqᴸ
produceWorldEvolutionᶜ₀
    (evolution-request-rightᶜ₀ fresh eqᴿ) =
  evolution-bind-rightᶜ₀ fresh eqᴿ
produceWorldEvolutionᶜ₀
    (evolution-request-both-preciseᶜ₀ represented eqᴸ eqᴿ) =
  evolution-bind-bothᶜ₀ represented eqᴸ eqᴿ
produceWorldEvolutionᶜ₀
    (evolution-request-both-dynamicᶜ₀
      represented A≠★ eqᴸ eqᴿ) =
  evolution-bind-both-starᶜ₀ represented A≠★ eqᴸ eqᴿ


-- `StoreChange` exposes only `keep` or `bind A`.  It does not expose the
-- right-only freshness proof, the paired allocation's `A ⊑ᵀ⟨ W ⟩ B`, or
-- the precise/dynamic choice and its `⇑ᵗ A ≢ ★` evidence.  These are the
-- exact extra facts the reduction/simulation producer must retain.  A bare
-- reduction step also carries no term contexts; a typed producer must supply
-- the displayed shift equalities (canonically `refl` when it builds them).
