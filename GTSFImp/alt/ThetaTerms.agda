module alt.ThetaTerms where

-- File Charter:
--   * Defines syntax with anchor contexts Θ separate from regular type
--     contexts Δ; no anchor form is added to Ty.
--   * Reuses Ty Θ only in anchor-telescope entries, where its variables name
--     earlier anchors.  Telescope lookup follows the TyStore idiom: an
--     equality witness records each weakening into the full context.
--   * Reveal/conceal bind and anti-bind only Δ, while ν/wk bind and anti-bind
--     only Θ; their node data connects the two orthogonal index spaces.
--   * Provides syntax and the minimal telescope/classifier structure only;
--     typing and structural operations belong to later chunks.

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Primitives
open import Consistency
open import alt.Conversion

------------------------------------------------------------------------
-- Anchor telescopes
------------------------------------------------------------------------

AnchorCtx : Set
AnchorCtx = ℕ

private
  variable
    Θ Θ′ : AnchorCtx
    Δ : TyCtx

data Tele : AnchorCtx → Set where
  tele-empty : Tele zero
  tele-bind : ∀ {Θ} → Tele Θ → Ty Θ → Tele (suc Θ)

infix 4 _∋ν_⦂_

data _∋ν_⦂_ : ∀ {Θ} → Tele Θ → TyVar Θ → Ty Θ → Set where
  Zν : ∀ {Θ} {Ξ : Tele Θ} {R : Ty Θ} {S : Ty (suc Θ)}
    → S ≡ ⇑ᵗ R
    → tele-bind Ξ R ∋ν zero ⦂ S

  Sν : ∀ {Θ} {Ξ : Tele Θ} {α : TyVar Θ} {R A : Ty Θ}
      {S : Ty (suc Θ)}
    → Ξ ∋ν α ⦂ R
    → S ≡ ⇑ᵗ R
    → tele-bind Ξ A ∋ν suc α ⦂ S

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_˙_
infixl 7 _·_
infix  5 Λ_
infixl 7 _⦂∀_[_]
infixl 7 _⟨_⟩
infixl 7 _↑[_≔_]_ _↓[_≔_]_
infixl 6 _⊕[_]_
infix  5 ν[_]_
infix  9 `_

Var : Set
Var = ℕ

data Term : AnchorCtx → TyCtx → Set where
  `_      : Var → Term Θ Δ
  ƛ_˙_    : Ty Δ → Term Θ Δ → Term Θ Δ
  _·_     : Term Θ Δ → Term Θ Δ → Term Θ Δ
  Λ_      : Term Θ (suc Δ) → Term Θ Δ
  _⦂∀_[_] : Term Θ Δ → Ty (suc Δ) → Ty Δ → Term Θ Δ
  $       : Const → Term Θ Δ
  _⊕[_]_  : Term Θ Δ → Prim → Term Θ Δ → Term Θ Δ
  _⟨_⟩    : Term Θ Δ → {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Term Θ Δ

  _↑[_≔_]_ : Term Θ (suc Δ)
    → TyVar (suc Δ) → TyVar Θ → Reveal → Term Θ Δ

  _↓[_≔_]_ : Term Θ Δ
    → TyVar (suc Δ) → TyVar Θ → Conceal → Term Θ (suc Δ)

  ν[_]_ : Ty Θ → Term (suc Θ) Δ → Term Θ Δ

  blame : Term Θ Δ

------------------------------------------------------------------------
-- Anchor-variable renaming
------------------------------------------------------------------------

-- Anchors occur only in node data (ν entries and reveal/conceal anchor
-- references), so renaming them leaves types, evidence, and conversion
-- shapes untouched.  Floats shift frame siblings with `shiftᶿ` (design
-- decision 2026-08-23: eager anchor shifts at extrusion, no wk node).

renameᶿ : (TyVar Θ → TyVar Θ′) → Term Θ Δ → Term Θ′ Δ
renameᶿ ρ (` x) = ` x
renameᶿ ρ (ƛ A ˙ M) = ƛ A ˙ renameᶿ ρ M
renameᶿ ρ (L · M) = renameᶿ ρ L · renameᶿ ρ M
renameᶿ ρ (Λ M) = Λ renameᶿ ρ M
renameᶿ ρ (L ⦂∀ C [ A ]) = renameᶿ ρ L ⦂∀ C [ A ]
renameᶿ ρ ($ κ) = $ κ
renameᶿ ρ (L ⊕[ op ] M) = renameᶿ ρ L ⊕[ op ] renameᶿ ρ M
renameᶿ ρ (M ⟨ c ⟩) = renameᶿ ρ M ⟨ c ⟩
renameᶿ ρ (M ↑[ Y ≔ α ] c) = renameᶿ ρ M ↑[ Y ≔ ρ α ] c
renameᶿ ρ (M ↓[ Y ≔ α ] c) = renameᶿ ρ M ↓[ Y ≔ ρ α ] c
renameᶿ ρ (ν[ A ] M) = ν[ renameᵗ ρ A ] renameᶿ (extᵗ ρ) M
renameᶿ ρ blame = blame

shiftᶿ : Term Θ Δ → Term (suc Θ) Δ
shiftᶿ = renameᶿ suc
