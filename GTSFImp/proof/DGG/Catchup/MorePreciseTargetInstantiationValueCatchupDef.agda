{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePreciseTargetInstantiationValueCatchupDef where

-- File Charter:
--   * States the exposed target-only beta-instantiation catch-up case after
--     generic source wrappers have been stripped by the target-cast worker.
--   * Exposes the allocation trace, evolved world, final value, and CTI
--     evidence directly, without a result record or fuel-indexed wrapper.
--   * Its premise relates the two values at the target universal input type;
--     the conclusion executes the instantiation cast to its result type.
--   * Isolates the genuine induction through polymorphic value spines.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_; instᵐ; inst_)
import Data.Fin as Fin
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⟨_⟩)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePreciseTargetInstantiationValueCatchupᵀ : Set
MorePreciseTargetInstantiationValueCatchupᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν′ : Env∼ Δᴿ} {c′ : instᵐ ν′ ⊢ B ∼ ⇑ᵗ B′}
    ⦃ Bnv : NonVar B ⦄ ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    {B′≠★ : B′ ≢ ★}
    {p : A ⊑ᵀ⟨ γ ⟩ `∀ B}
    {q : A ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → γ ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ W′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (V′ ⟨ (inst c′) B′≠★ ⟩ —↠[ χsᴿ ] W′)
      × Value W′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² V ⊑ W′ ∶ q)
