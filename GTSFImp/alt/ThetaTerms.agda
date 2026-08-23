module alt.ThetaTerms where

-- File Charter:
--   * Defines syntax with anchor position counts Θ separate from regular
--     type contexts Δ; no anchor form is added to Ty, and no Ty is ever
--     indexed by an anchor space.
--   * The telescope holds the anchor-to-representation bindings.  Each
--     representation is an ordinary type over the TYPE CONTEXT generated
--     by the telescope prefix before it: a reference to an earlier anchor
--     is an ordinary type variable of that context, and a representation's
--     ∀-local binders extend that context as usual.  Telescope lookup
--     follows the TyStore idiom: an equality witness records each
--     weakening into the full context.
--   * Reveal/conceal bind and anti-bind only Δ, while ν binds Θ; node data
--     (anchor references) are telescope positions, identified with the
--     telescope's context length at the typing context.
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

-- Indexed by the type context its entries generate: the entry added by
-- tele-bind is a type over the context of the rest of the telescope.
data Tele : TyCtx → Set where
  tele-empty : Tele zero
  tele-bind : ∀ {Δᵀ} → Tele Δᵀ → Ty Δᵀ → Tele (suc Δᵀ)

infix 4 _∋ν_⦂_

data _∋ν_⦂_ : ∀ {Δᵀ} → Tele Δᵀ → TyVar Δᵀ → Ty Δᵀ → Set where
  Zν : ∀ {Δᵀ} {Ξ : Tele Δᵀ} {R : Ty Δᵀ} {S : Ty (suc Δᵀ)}
    → S ≡ ⇑ᵗ R
    → tele-bind Ξ R ∋ν zero ⦂ S

  Sν : ∀ {Δᵀ} {Ξ : Tele Δᵀ} {α : TyVar Δᵀ} {R A : Ty Δᵀ}
      {S : Ty (suc Δᵀ)}
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
