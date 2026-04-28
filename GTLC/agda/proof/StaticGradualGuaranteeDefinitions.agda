module proof.StaticGradualGuaranteeDefinitions where

-- File Charter:
--   * Private helper definitions for the static gradual guarantee proof.
--   * Defines binder extension for source context imprecision.
--   * Depends on the public statement-level context-imprecision relation.

open import Data.Product using (proj₁; proj₂; _,_)
open import Agda.Builtin.List using (_∷_)
open import Agda.Builtin.Nat using (zero; suc)

open import Types
open import Contexts

extend-⊑ˢ
  : ∀ {Γ Γ′ A A′}
  → A′ ⊑ A
  → Γ ⊑ˢ Γ′
  → (A ∷ Γ) ⊑ˢ (A′ ∷ Γ′)
extend-⊑ˢ {A′ = A₀} A′⊑A Γ⊑Γ′ zero A Z = A₀ , Z , A′⊑A
extend-⊑ˢ A′⊑A Γ⊑Γ′ (suc x) B (S ∋x) =
  Γ⊑Γ′ x B ∋x .proj₁
  , S (Γ⊑Γ′ x B ∋x .proj₂ .proj₁)
  , Γ⊑Γ′ x B ∋x .proj₂ .proj₂
