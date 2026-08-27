{-# OPTIONS --safe #-}

module proof.DGG.TransportTermImprecisionDef where

-- File Charter:
--   * States transport of cast-term imprecision through canonical multi-world
--     evolution.
--   * Applies the source and target store-change traces directly to the terms.
--   * Uses the type transport computed by the same evolution evidence.
--   * Contains no transport proof.

open import Types using (Ty)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using (StoreChanges; applyTerms)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (CtxChange; WorldEvolution; evolution-⊑ᵀ)
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution; multi-⊑ᵀ; ctx-change-term-value)


TransportTermImprecisionStepᵀ : Set
TransportTermImprecisionStepᵀ = ∀
    {Γᴸ Γᴿ Γᴸ′ Γᴿ′ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {γ′ : Γᴸ′ ⊑ᶜ Γᴿ′}
    {stepᴸ : CtxChange Γᴸ Γᴸ′}
    {stepᴿ : CtxChange Γᴿ Γᴿ′}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (evol : WorldEvolution
      {W = γ} {W′ = γ′} stepᴸ stepᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ′ ⊢² ctx-change-term-value stepᴸ M
      ⊑ ctx-change-term-value stepᴿ M′ ∶ evolution-⊑ᵀ evol p


TransportTermImprecisionᵀ : Set
TransportTermImprecisionᵀ = ∀
    {Γᴸ Γᴿ Γᴸ′ Γᴿ′ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {γ′ : Γᴸ′ ⊑ᶜ Γᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Γᴸ) (Δᵉ Γᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′)}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (evol : MultiWorldEvolution
      {W = γ} {W′ = γ′} χsᴸ χsᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ′ ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
      ∶ multi-⊑ᵀ evol p
