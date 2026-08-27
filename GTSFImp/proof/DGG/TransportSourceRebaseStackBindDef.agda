{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceRebaseStackBindDef where

-- File Charter:
--   * States source-only allocation transport at the top of a balanced
--     source-rebase stack.
--   * The stack supplies the open reveal/conceal balance that is unavailable
--     to the zero-rebase source-bind transport.
--   * This is the one genuine structural CTI induction needed by canonical
--     source-rebase-stack transport.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Types using (Ty)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import CastTerms using (Term; ⟨_,_,_⟩)
open import Reduction using (applyTerms)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebaseStackDef using
  ( SourceRebaseStack
  ; stack-evolution-bind-left
  ; stack-top-evolution
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (multi-⊑ᵀ)


TransportSourceRebaseStackBindᵀ : Set
TransportSourceRebaseStackBindᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)}
    {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {stack : SourceRebaseStack γ⁰ γ}
    {C : Ty Δᴸ} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (Γᴸ⁺≡⁰ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → (Γᴸ⁺≡ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → γ ⊢² M ⊑ M′ ∶ p
  → (γ ▻ᶜ bind-left-changeᶜ C Γᴸ⁺≡) ⊢²
      applyTerms (Reduction.bind C Reduction.∷ Reduction.[]) M ⊑ M′
      ∶ multi-⊑ᵀ
        (stack-top-evolution
          (stack-evolution-bind-left {stack = stack}
            C Γᴸ⁺≡⁰ Γᴸ⁺≡)) p
