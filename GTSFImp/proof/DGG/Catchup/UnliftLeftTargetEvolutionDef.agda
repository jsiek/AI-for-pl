{-# OPTIONS --safe #-}

module proof.DGG.Catchup.UnliftLeftTargetEvolutionDef where

-- File Charter:
--   * States normalization of target-only world evolution beneath a protected
--     left type scope.
--   * Returns the corresponding outer evolution and transports CTI to the
--     canonical left lift of its final world.
--   * Isolates the center-swap induction created when chronological target
--     allocations cross the protected left binder.
--   * Contains no lambda reconstruction, catch-up result, or wrapper record.

open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; ⟨_,_,_⟩; ⇑ᵉᵗ)
open import Reduction using (StoreChanges; applyTys)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


UnliftLeftTargetEvolutionᵀ : Set
UnliftLeftTargetEvolutionᵀ = ∀ {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {γᵇ : ⇑ᵉᵗ ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {M : Term (suc Δᴸ)} {M′ : Term Δᴿ′}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵀ⟨ γᵇ ⟩ applyTys χsᴿ B}
  → openFramesᶜ γ ≡ []
  → MultiWorldEvolution {W = liftLeftᶜ γ} {W′ = γᵇ} []ˢ χsᴿ
  → γᵇ ⊢² M ⊑ M′ ∶ p
  → Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ A ⊑ᵀ⟨ liftLeftᶜ γ′ ⟩ applyTys χsᴿ B ]
      MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (liftLeftᶜ γ′ ⊢² M ⊑ M′ ∶ r)
