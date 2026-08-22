module LR-narrow.Context.UniversalsFuture where

-- File Charter:
--   * Proves Kripke monotonicity of paired-universal elimination.
--   * Rebases each future binder extension over the earlier interpretation.
--   * Contains exactly one exported theorem.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import ImprecisionWf using (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter using (Value)
open import LR-narrow.Context.PairedBinderRebase
open import LR-narrow.LogicalRelation using (UniversalsRelated)
open import LR-narrow.World
open import Types using (Ty; TyCtx)

universals-related-future : ∀
    {Φ Δᴸ Δᴿ A A′}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {k : ℕ} {V V′ : Value}
  → J ⊒ⁱ I
  → UniversalsRelated p I k V V′
  → UniversalsRelated p J k V V′
universals-related-future {k = zero} J⊒I related = tt
universals-related-future {k = suc k} J⊒I (head , tail) =
  (λ extension → head (paired-binder-rebase J⊒I extension)) ,
  universals-related-future J⊒I tail
