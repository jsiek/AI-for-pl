module LR-narrow.ClosingSubstitutionProperties where

-- File Charter:
--   * Exposes lookup, typing, projection, and future-transport theorems for
--     closing substitutions.
--   * Keeps theorem statements at the public LR boundary.
--   * Delegates proof scripts to proof.LR-narrow.ClosingSubstitution.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; Σ-syntax)

open import Types
open import TyStore
import TermCtx as T
open import CastTerms
open import proof.TermInTermSubst using (SubstWf)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
import proof.LR-narrow.ClosingSubstitution as Proof

value-imprecision-endpoints : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → TypedEndpoints W p Vᴵ Vᴾ
value-imprecision-endpoints = Proof.value-imprecision-endpoints

closing-lookup-value : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {x A}
    (γ : ClosingSubstitution Σ Γ)
  → Γ T.∋ x ⦂ A
  → Value (lookupClosing γ x)
closing-lookup-value = Proof.closing-lookup-value

closing-lookup-typing : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {x A}
    (γ : ClosingSubstitution Σ Γ)
  → Γ T.∋ x ⦂ A
  → ⟨ Δ , Σ , [] ⟩ ⊢ lookupClosing γ x ⦂ A
closing-lookup-typing = Proof.closing-lookup-typing

closing-substitution-wf : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ)
  → SubstWf Δ Σ Γ [] (closingSubstitution γ)
closing-substitution-wf = Proof.closing-substitution-wf

close-preserves-value : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) {V}
  → Value V
  → Value (close γ V)
close-preserves-value = Proof.close-preserves-value

close-preserves-typing : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) {M A}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , [] ⟩ ⊢ close γ M ⦂ A
close-preserves-typing = Proof.close-preserves-typing

precise-open-typing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} {M : Term Δᴾ} {A : Ty Δᴾ}
    (W≼W′ : Future W W′)
  → ⟨ Δᴾ , preciseStore (core W) , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴾ′ , preciseStore (core W′) ,
        liftPreciseContext W≼W′ Γ ⟩
      ⊢ liftPreciseTerm W≼W′ M ⦂ liftPreciseTy W≼W′ A
precise-open-typing-future = Proof.precise-open-typing-future

imprecise-open-typing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} {M : Term Δᴵ} {A : Ty Δᴵ}
    (W≼W′ : Future W W′)
  → ⟨ Δᴵ , impreciseStore (core W) , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴵ′ , impreciseStore (core W′) ,
        liftImpreciseContext W≼W′ Γ ⟩
      ⊢ liftImpreciseTerm W≼W′ M ⦂ liftImpreciseTy W≼W′ A
imprecise-open-typing-future = Proof.imprecise-open-typing-future

preciseClosingSubstitution : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W}
  → RelatedClosingSubstitutions W k Γ
  → ClosingSubstitution (preciseStore (core W)) (preciseContext Γ)
preciseClosingSubstitution = Proof.preciseClosingSubstitution

impreciseClosingSubstitution : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W}
  → RelatedClosingSubstitutions W k Γ
  → ClosingSubstitution (impreciseStore (core W)) (impreciseContext Γ)
impreciseClosingSubstitution = Proof.impreciseClosingSubstitution

related-closing-lookup : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W} {x Aᴾ Aᴵ p}
    (x∈ : Γ ∋ᴿ x ⦂ context-imp Aᴾ Aᴵ p)
    (γ : RelatedClosingSubstitutions W k Γ)
  → (∀ j → j ≤ k → ValueImprecision W p j
        (lookupClosing (impreciseClosingSubstitution γ) x)
        (lookupClosing (preciseClosingSubstitution γ) x))
related-closing-lookup = Proof.related-closing-lookup

lift-context-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : ContextImprecision W} {x Aᴾ Aᴵ p}
    (W≼W′ : Future W W′)
  → Γ ∋ᴿ x ⦂ context-imp Aᴾ Aᴵ p
  → liftContextImprecision W≼W′ Γ ∋ᴿ x ⦂
      context-imp (liftPreciseTy W≼W′ Aᴾ)
        (liftImpreciseTy W≼W′ Aᴵ) (liftLocalImprecision W≼W′ p)
lift-context-lookup = Proof.lift-context-lookup

related-closing-downward : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {j k : ℕ}
    {Γ : ContextImprecision W}
  → j ≤ k
  → RelatedClosingSubstitutions W k Γ
  → RelatedClosingSubstitutions W j Γ
related-closing-downward = Proof.related-closing-downward

related-closing-bind : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W} {Aᴾ Aᴵ}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
  → (∀ j → j ≤ k →
      ValueImprecision W′ (liftCenterImprecision W≼W′ p) j Vᴵ Vᴾ)
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ Γ)
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′
        (context-imp Aᴾ Aᴵ p ∷ Γ))
related-closing-bind = Proof.related-closing-bind

related-closing-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k : ℕ} {Γ : ContextImprecision W₀}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
  → RelatedClosingSubstitutions W₂ k
      (liftContextImprecision W₁≼W₂
        (liftContextImprecision W₀≼W₁ Γ))
  → RelatedClosingSubstitutions W₂ k
      (liftContextImprecision (future-trans W₀≼W₁ W₁≼W₂) Γ)
related-closing-trans = Proof.related-closing-trans

shiftClosingBind : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {B : Ty Δ}
  → ClosingSubstitution Σ Γ
  → ClosingSubstitution (store-bind Σ B) (T.⇑ᶜ Γ)
shiftClosingBind = Proof.shiftClosingBind

precise-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} (W≼W′ : Future W W′)
  → ClosingSubstitution (preciseStore (core W)) Γ
  → ClosingSubstitution (preciseStore (core W′))
      (liftPreciseContext W≼W′ Γ)
precise-closing-future = Proof.precise-closing-future

imprecise-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} (W≼W′ : Future W W′)
  → ClosingSubstitution (impreciseStore (core W)) Γ
  → ClosingSubstitution (impreciseStore (core W′))
      (liftImpreciseContext W≼W′ Γ)
imprecise-closing-future = Proof.imprecise-closing-future

related-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W}
    (W≼W′ : Future W W′)
  → RelatedClosingSubstitutions W k Γ
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ Γ)
related-closing-future = Proof.related-closing-future
