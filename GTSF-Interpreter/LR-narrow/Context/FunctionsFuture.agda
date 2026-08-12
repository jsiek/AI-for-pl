module LR-narrow.Context.FunctionsFuture where

-- File Charter:
--   * Proves Kripke monotonicity of the function-elimination clause.
--   * Uses transitivity to view every future test as a test of the old world.
--   * Contains exactly one exported theorem.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (Value)
open import LR-narrow.Context.KripkeTrans
open import LR-narrow.LogicalRelation using (FunctionsRelated)
open import LR-narrow.World
open import Types using (Ty; TyCtx)

functions-related-future : ∀
    {Φ Δᴸ Δᴿ A A′ B B′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {k : ℕ} {V V′ : Value}
  → J ⊒ⁱ I
  → FunctionsRelated p q I k V V′
  → FunctionsRelated p q J k V V′
functions-related-future {k = zero} J⊒I related = tt
functions-related-future {k = suc k} J⊒I (head , tail) =
  (λ K K⊒J argument →
      head K (interpretation-⊒ⁱ-trans K⊒J J⊒I) argument) ,
  functions-related-future J⊒I tail
