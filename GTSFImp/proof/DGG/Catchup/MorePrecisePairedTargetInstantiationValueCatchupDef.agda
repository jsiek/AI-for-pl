{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePrecisePairedTargetInstantiationValueCatchupDef where

-- File Charter:
--   * States the whole paired source-cast/target-instantiation catch-up
--     branch after generic source wrappers have been stripped.
--   * Keeps the source inert cast in the final CTI evidence instead of
--     demanding a generally false intermediate input-to-output type edge.
--   * Exposes allocation, evolution, result value, and final CTI directly.
--   * Isolates the genuine induction through paired polymorphic value spines.
--   * Contains no classifier, residual family, fuel, or result wrapper.

open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import TyStore using (TyStore)
open import Consistency using (Env∼; _⊢_∼_; instᵐ; inst_)
import Data.Fin as Fin
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⟨_⟩)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


MorePrecisePairedTargetInstantiationValueCatchupᵀ : Set
MorePrecisePairedTargetInstantiationValueCatchupᵀ = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {C A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {νᴸ : Env∼ Δᴸ} {νᴿ : Env∼ Δᴿ}
    {cᴸ : νᴸ ⊢ C ∼ A} {cᴿ : instᵐ νᴿ ⊢ B ∼ ⇑ᵗ B′}
    ⦃ Bnv : NonVar B ⦄ ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    {B′≠★ : B′ ≢ ★}
    {p : C ⊑ᵀ⟨ γ ⟩ `∀ B} {q : A ⊑ᵀ⟨ γ ⟩ B′}
  → openFramesᶜ γ ≡ []
  → γ ⊢² V ⊑ V′ ∶ p
  → Inert cᴸ
  → Value V
  → Value V′
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ W′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
      (V′ ⟨ (inst cᴿ) B′≠★ ⟩ —↠[ χsᴿ ] W′)
      × Value W′
      × MultiWorldEvolution {W = γ} {W′ = γ′} []ˢ χsᴿ
      × (γ′ ⊢² V ⟨ cᴸ ⟩ ⊑ W′ ∶ r)
