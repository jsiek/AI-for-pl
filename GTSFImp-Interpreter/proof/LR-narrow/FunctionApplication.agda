module proof.LR-narrow.FunctionApplication where

-- File Charter:
--   * Eliminates a related function value at a related value argument.
--   * Makes the two step-index decrements of the function value clause
--     explicit.
--   * Contains no evaluation or substitution reasoning.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation

related-function-application : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    {k : ℕ} {Vᴵ Uᴵ : Term Δᴵ} {Vᴾ Uᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p q) (suc (suc k)) Vᴵ Vᴾ
  → ValueImprecision W p (suc k) Uᴵ Uᴾ
  → ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ · Uᴵ) (Vᴾ · Uᴾ)
related-function-application {W = W} (endpoints , head , tail) argument =
  head W future-refl argument
