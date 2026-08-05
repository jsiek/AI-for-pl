module Simulation.Coercion.InterpreterCoercionComputation where

-- File Charter:
--   * Public pointwise equations for explicit coercion computations.
--   * States sequencing and polymorphic instantiation without small steps.
--   * Delegates fuel case analysis to a focused private proof module.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Relation.Nullary using (yes; no)

open import Coercions renaming
  ( id to idᶜ
  ; _︔_ to _︔ᶜ_
  ; _↦_ to _↦ᶜ_
  ; `∀ to ∀ᶜ
  ; _! to _!ᶜ
  ; _？ to _？ᶜ
  ; unseal to unsealᶜ
  ; gen to genᶜ
  ; inst to instᶜ
  )
open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
open import Types
import proof.InterpreterCoercionComputationProof as Proof

coerce-id-computation :
  ∀ {W θ A V} n →
  coerceValue W θ (idᶜ A) V n ≡
  immediateReturn W V n
coerce-id-computation =
  Proof.coerce-id-computation

coerce-sequence-computation :
  ∀ {W θ c d V} n →
  coerceValue W θ (c ︔ᶜ d) V n ≡
  sequence W
    (coerceValue W θ c V)
    (λ U Q → coerceValue U θ d Q)
    n
coerce-sequence-computation =
  Proof.coerce-sequence-computation

coerce-function-computation :
  ∀ {W θ p q V} n →
  coerceValue W θ (p ↦ᶜ q) V n ≡
  immediateReturn W (function-proxy p q θ V) n
coerce-function-computation =
  Proof.coerce-function-computation

coerce-forall-computation :
  ∀ {W θ c V} n →
  coerceValue W θ (∀ᶜ c) V n ≡
  immediateReturn W (forall-proxy c θ V) n
coerce-forall-computation =
  Proof.coerce-forall-computation

coerce-tag-computation :
  ∀ {W θ G} {runtime-ground : RuntimeGround θ G} {tag V} →
  ground? θ G ≡ yes runtime-ground →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just tag →
  ∀ n →
  coerceValue W θ (G !ᶜ) V n ≡
  immediateReturn W
    (tagged (runtime-ground-syntax runtime-ground) θ V) n
coerce-tag-computation =
  Proof.coerce-tag-computation

coerce-untag-computation :
  ∀ {W θ G H} {runtime-ground : RuntimeGround θ G}
    {gH : Ground H}
    {expected actual σ V}
    (match : expected ≡ actual) →
  ground? θ G ≡ yes runtime-ground →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  ∀ n →
  coerceValue W θ (G ？ᶜ) (tagged gH σ V) n ≡
  immediateReturn W V n
coerce-untag-computation =
  Proof.coerce-untag-computation

coerce-untag-blame-computation :
  ∀ {W θ G H} {runtime-ground : RuntimeGround θ G}
    {gH : Ground H}
    {expected actual σ V}
    (expected≢actual : expected ≡ actual → Data.Empty.⊥) →
  ground? θ G ≡ yes runtime-ground →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  ∀ n →
  coerceValue W θ (G ？ᶜ) (tagged gH σ V) n ≡
  immediateBlame W n
coerce-untag-blame-computation =
  Proof.coerce-untag-blame-computation

coerce-unseal-computation :
  ∀ {W θ X A expected actual V} →
  lookup θ X ≡ just (seal-name expected) →
  expected ≡ actual →
  ∀ n →
  coerceValue W θ (unsealᶜ X A) (sealed actual V) n ≡
  immediateReturn W V n
coerce-unseal-computation =
  Proof.coerce-unseal-computation

coerce-generalization-computation :
  ∀ {W θ A c V} n →
  coerceValue W θ (genᶜ A c) V n ≡
  immediateReturn W (generalized A c θ V) n
coerce-generalization-computation =
  Proof.coerce-generalization-computation

coerce-instantiation-computation :
  ∀ {W θ B c V} n →
  coerceValue W θ (instᶜ B c) V n ≡
  sequence W
    (instantiateValue
      (allocate W ★ θ) (freshSealName W) V)
    (λ U Q →
      coerceValue U
        (seal-name (freshSealName W) ∷ θ) c Q)
    n
coerce-instantiation-computation =
  Proof.coerce-instantiation-computation
