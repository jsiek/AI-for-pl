module LR-narrow.FunctionApplication where

-- File Charter:
--   * Exposes elimination of related function values.
--   * Preserves the positive call index exposed by FunctionsRelated.
--   * Delegates the proof to proof.LR-narrow.FunctionApplication.

open import Data.Nat using (ℕ; suc)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.FunctionApplication as Proof

related-function-application : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    {k : ℕ} {Vᴵ Uᴵ : Term Δᴵ} {Vᴾ Uᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p q) (suc k) Vᴵ Vᴾ
  → ValueImprecision W p (suc k) Uᴵ Uᴾ
  → ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ · Uᴵ) (Vᴾ · Uᴾ)
related-function-application = Proof.related-function-application
