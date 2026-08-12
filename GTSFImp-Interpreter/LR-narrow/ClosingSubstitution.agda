module LR-narrow.ClosingSubstitution where

-- File Charter:
--   * Defines typed substitutions that close term variables before evaluation.
--   * Defines paired closing substitutions whose entries satisfy the value LR.
--   * Defines endpoint-context lifting along future worlds.
--   * Contains no lookup, typing, or future-transport proofs.

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≤_)

open import Types
open import TyStore
open import TermCtx using (TermCtx)
open import CastTerms
open import LR-narrow.World
open import LR-narrow.LogicalRelation

------------------------------------------------------------------------
-- Typed closing substitutions
------------------------------------------------------------------------

data ClosingSubstitution {Δ : TyCtx} (Σ : TyStore Δ) :
    TermCtx Δ → Set where
  closing-empty : ClosingSubstitution Σ []

  closing-cons : ∀ {Γ A V}
    → Value V
    → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
    → ClosingSubstitution Σ Γ
    → ClosingSubstitution Σ (A ∷ Γ)

lookupClosing : ∀ {Δ : TyCtx} {Σ : TyStore Δ} {Γ : TermCtx Δ}
  → ClosingSubstitution Σ Γ
  → ℕ
  → Term Δ
lookupClosing closing-empty x = blame
lookupClosing (closing-cons {V = V} vV V⊢ γ) zero = V
lookupClosing (closing-cons vV V⊢ γ) (suc x) = lookupClosing γ x

closingSubstitution : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : TermCtx Δ}
  → ClosingSubstitution Σ Γ
  → Subst Δ
closingSubstitution γ = lookupClosing γ

close : ∀ {Δ : TyCtx} {Σ : TyStore Δ} {Γ : TermCtx Δ}
  → ClosingSubstitution Σ Γ
  → Term Δ
  → Term Δ
close γ M = subst (closingSubstitution γ) M

------------------------------------------------------------------------
-- Related closing substitutions
------------------------------------------------------------------------

record ContextImprecisionEntry {Δᴾ Δᴵ Δᶜ : TyCtx}
    (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor context-imp
  field
    preciseType : Ty Δᴾ
    impreciseType : Ty Δᴵ
    typeImprecision : preciseType ⊑ᵂ⟨ core W ⟩ impreciseType

open ContextImprecisionEntry public

ContextImprecision : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
  → World Δᴾ Δᴵ Δᶜ
  → Set
ContextImprecision W = List (ContextImprecisionEntry W)

preciseContext : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
  → ContextImprecision W
  → TermCtx Δᴾ
preciseContext = map preciseType

impreciseContext : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
  → ContextImprecision W
  → TermCtx Δᴵ
impreciseContext = map impreciseType

infix 4 _∋ᴿ_⦂_

data _∋ᴿ_⦂_ {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ} :
    ContextImprecision W → ℕ → ContextImprecisionEntry W → Set where
  Zᴿ : ∀ {Γ Aᴾ Aᴵ p}
    → (context-imp Aᴾ Aᴵ p ∷ Γ) ∋ᴿ zero ⦂ context-imp Aᴾ Aᴵ p

  Sᴿ : ∀ {Γ e e′ x}
    → Γ ∋ᴿ x ⦂ e
    → (e′ ∷ Γ) ∋ᴿ suc x ⦂ e

data RelatedClosingSubstitutions {Δᴾ Δᴵ Δᶜ : TyCtx}
    (W : World Δᴾ Δᴵ Δᶜ) (k : ℕ) :
    ContextImprecision W → Set₁ where
  related-empty : RelatedClosingSubstitutions W k []

  related-cons : ∀ {Γ Aᴾ Aᴵ Vᴾ Vᴵ}
    → (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    → (∀ j → j ≤ k → ValueImprecision W p j Vᴵ Vᴾ)
    → RelatedClosingSubstitutions W k Γ
    → RelatedClosingSubstitutions W k
        (context-imp Aᴾ Aᴵ p ∷ Γ)

------------------------------------------------------------------------
-- Endpoint contexts in future worlds
------------------------------------------------------------------------

liftPreciseContext : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TermCtx Δᴾ
  → TermCtx Δᴾ′
liftPreciseContext W≼W′ [] = []
liftPreciseContext W≼W′ (A ∷ Γ) =
  liftPreciseTy W≼W′ A ∷ liftPreciseContext W≼W′ Γ

liftImpreciseContext : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TermCtx Δᴵ
  → TermCtx Δᴵ′
liftImpreciseContext W≼W′ [] = []
liftImpreciseContext W≼W′ (A ∷ Γ) =
  liftImpreciseTy W≼W′ A ∷ liftImpreciseContext W≼W′ Γ

liftContextImprecision : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → (W≼W′ : Future W W′)
  → ContextImprecision W
  → ContextImprecision W′
liftContextImprecision W≼W′ [] = []
liftContextImprecision W≼W′ (context-imp Aᴾ Aᴵ p ∷ Γ) =
  context-imp (liftPreciseTy W≼W′ Aᴾ)
    (liftImpreciseTy W≼W′ Aᴵ)
    (liftLocalImprecision W≼W′ p)
    ∷ liftContextImprecision W≼W′ Γ
