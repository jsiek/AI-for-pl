module Runtime.InterpreterTypeEnvironmentRealizationProperties where

-- File Charter:
--   * Public eliminations for proof-relevant type-environment realization.
--   * Recovers source-dynamic seal provenance from a concrete lookup.
--   * Delegates the proof to a reduction-free private module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)

open import ImprecisionWf using (_ˣ⊑★)
open import Interpreter
open import Runtime.InterpreterTypeEnvironmentRealization
import proof.InterpreterTypeEnvironmentRealizationPropertiesProof as Proof

open RelatedWorlds

source-dynamic-seal-lookup :
  ∀ {W W′ θ θ′ X α}
    {R : WorldRelation W W′} →
  AssumptionRealization R θ θ′ (X ˣ⊑★) →
  lookup θ X ≡ just (seal-name α) →
  LeftDynamicSeal R α
source-dynamic-seal-lookup =
  Proof.source-dynamic-seal-lookup
