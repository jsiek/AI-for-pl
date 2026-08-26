module LR-narrow.Context.RightUniversalsFuture where

-- File Charter:
--   * Proves Kripke monotonicity of precise-right universal elimination.
--   * Treats its provisional computation clause opaquely while rebasing it.
--   * Contains exactly one exported theorem.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter using (Value)
open import LR-narrow.Context.RightBinderRebase
open import LR-narrow.LogicalRelation using (RightUniversalsRelated)
open import LR-narrow.World
open import Types using (Ty; TyCtx)

right-universals-related-future : ∀
    {Φ Δᴸ Δᴿ A A′}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {k : ℕ} {V V′ : Value}
  → J ⊒ⁱ I
  → RightUniversalsRelated p I k V V′
  → RightUniversalsRelated p J k V V′
right-universals-related-future {k = zero} J⊒I related extension =
  related (right-binder-rebase J⊒I extension)
right-universals-related-future {k = suc k} J⊒I (head , tail) =
  (λ extension → head (right-binder-rebase J⊒I extension)) ,
  right-universals-related-future J⊒I tail
