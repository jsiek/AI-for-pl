module StaticGradualGuarantee where

-- File Charter:
--   * Public wrapper for the static gradual guarantee theorem.
--   * Proof details are implemented in `proof/StaticGradualGuarantee.agda`.

open import Data.Product using (_×_; ∃; ∃-syntax)
open import Agda.Builtin.List using (_∷_)
open import Types
open import Contexts
open import GTLC

import proof.StaticGradualGuarantee as Proof

_⊑ˢ_ : Ctx → Ctx → Set
_⊑ˢ_ = Proof._⊑ˢ_

extend-⊑ˢ : ∀ {Γ Γ′ A A′} → A′ ⊑ A → Γ ⊑ˢ Γ′ → (A ∷ Γ) ⊑ˢ (A′ ∷ Γ′)
extend-⊑ˢ = Proof.extend-⊑ˢ

static-gradual-guarantee
  : ∀ {Γ Γ′ M M′ A}
  → Γ ⊢ M ⦂ A
  → M′ ⊑ᵀ M
  → Γ ⊑ˢ Γ′
  → ∃[ A′ ] (Γ′ ⊢ M′ ⦂ A′) × (A′ ⊑ A)
static-gradual-guarantee = Proof.static-gradual-guarantee
