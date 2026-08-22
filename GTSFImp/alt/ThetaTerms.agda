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
    Θ : AnchorCtx
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
-- Regular-variable classifier
------------------------------------------------------------------------

data Binding (Θ : AnchorCtx) : Set where
  ∀-bound : Binding Θ
  slot≔ : TyVar Θ → Binding Θ

infixr 5 _∷_

data Classifier (Θ : AnchorCtx) : TyCtx → Set where
  [] : Classifier Θ zero
  _∷_ : ∀ {Δ} → Binding Θ → Classifier Θ Δ
    → Classifier Θ (suc Δ)

lookupClassifier : Classifier Θ Δ → TyVar Δ → Binding Θ
lookupClassifier (b ∷ κ) zero = b
lookupClassifier (b ∷ κ) (suc X) = lookupClassifier κ X

insert∀ : Classifier Θ Δ → Classifier Θ (suc Δ)
insert∀ κ = ∀-bound ∷ κ

insertSlot : TyVar (suc Δ) → TyVar Θ
  → Classifier Θ Δ → Classifier Θ (suc Δ)
insertSlot zero α κ = slot≔ α ∷ κ
insertSlot (suc X) α (b ∷ κ) = b ∷ insertSlot X α κ

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
infix  5 ν[_]_ wk[_]_
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

  wk[_]_ : TyVar (suc Θ) → Term Θ Δ → Term (suc Θ) Δ

  blame : Term Θ Δ
