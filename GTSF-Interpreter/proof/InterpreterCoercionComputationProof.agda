module proof.InterpreterCoercionComputationProof where

-- File Charter:
--   * Proves pointwise computation equations for every coercion constructor.
--   * Exposes coercion sequencing and instantiation as explicit computations.
--   * Uses fuel case analysis only; no reduction semantics or adequacy result.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Nullary using (yes; no)

open import Coercions renaming
  ( id to idᶜ
  ; _︔_ to _︔ᶜ_
  ; _↦_ to _↦ᶜ_
  ; `∀ to ∀ᶜ
  ; _! to _!ᶜ
  ; _？ to _？ᶜ
  ; seal to sealᶜ
  ; unseal to unsealᶜ
  ; gen to genᶜ
  ; inst to instᶜ
  )
open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
open import Types

coerce-id-computation :
  ∀ {W θ A V} n →
  coerceValue W θ (idᶜ A) V n ≡
  immediateReturn W V n
coerce-id-computation zero =
  refl
coerce-id-computation (suc n) =
  refl

coerce-sequence-computation :
  ∀ {W θ c d V} n →
  coerceValue W θ (c ︔ᶜ d) V n ≡
  sequence W
    (coerceValue W θ c V)
    (λ U Q → coerceValue U θ d Q)
    n
coerce-sequence-computation zero =
  refl
coerce-sequence-computation {W} {θ} {c} {d} {V} (suc n)
    with coerceValue W θ c V n in head-eq
coerce-sequence-computation {W} {θ} {c} {d} {V} (suc n)
    | timed U =
  refl
coerce-sequence-computation {W} {θ} {c} {d} {V} (suc n)
    | blamed U =
  refl
coerce-sequence-computation {W} {θ} {c} {d} {V} (suc n)
    | failed U e =
  refl
coerce-sequence-computation {W} {θ} {c} {d} {V} (suc n)
    | returned U Q =
  refl

coerce-function-computation :
  ∀ {W θ p q V} n →
  coerceValue W θ (p ↦ᶜ q) V n ≡
  immediateReturn W (function-proxy p q θ V) n
coerce-function-computation zero =
  refl
coerce-function-computation (suc n) =
  refl

coerce-forall-computation :
  ∀ {W θ c V} n →
  coerceValue W θ (∀ᶜ c) V n ≡
  immediateReturn W (forall-proxy c θ V) n
coerce-forall-computation zero =
  refl
coerce-forall-computation (suc n) =
  refl

coerce-tag-computation :
  ∀ {W θ G} {runtime-ground : RuntimeGround θ G} {tag V} →
  ground? θ G ≡ yes runtime-ground →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just tag →
  ∀ n →
  coerceValue W θ (G !ᶜ) V n ≡
  immediateReturn W
    (tagged (runtime-ground-syntax runtime-ground) θ V) n
coerce-tag-computation ground-eq tag-eq zero =
  refl
coerce-tag-computation ground-eq tag-eq (suc n)
    rewrite ground-eq | tag-eq =
  refl

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
coerce-untag-computation match ground-eq expected-eq actual-eq zero =
  refl
coerce-untag-computation {expected = expected} refl ground-eq
    expected-eq actual-eq
    (suc n)
    rewrite ground-eq | expected-eq | actual-eq
    with expected ≟Tag expected
coerce-untag-computation {expected = expected} refl ground-eq
    expected-eq actual-eq
    (suc n) | yes refl =
  refl
coerce-untag-computation {expected = expected} refl ground-eq
    expected-eq actual-eq
    (suc n) | no expected≢expected =
  ⊥-elim (expected≢expected refl)

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
coerce-untag-blame-computation
    {expected = expected} {actual}
    expected≢actual ground-eq
    expected-eq actual-eq zero =
  refl
coerce-untag-blame-computation
    {expected = expected} {actual}
    expected≢actual ground-eq
    expected-eq actual-eq (suc n)
    rewrite ground-eq | expected-eq | actual-eq
    with expected ≟Tag actual
coerce-untag-blame-computation
    {expected = expected} {actual}
    expected≢actual ground-eq
    expected-eq actual-eq (suc n) | yes expected≡actual =
  ⊥-elim (expected≢actual expected≡actual)
coerce-untag-blame-computation
    {expected = expected} {actual}
    expected≢actual ground-eq
    expected-eq actual-eq (suc n) | no other-proof =
  refl

coerce-unseal-computation :
  ∀ {W θ X A expected actual V} →
  lookup θ X ≡ just (seal-name expected) →
  expected ≡ actual →
  ∀ n →
  coerceValue W θ (unsealᶜ X A) (sealed actual V) n ≡
  immediateReturn W V n
coerce-unseal-computation lookup-eq refl zero =
  refl
coerce-unseal-computation
    {expected = expected} lookup-eq refl (suc n)
    rewrite lookup-eq
    with expected ≟SealName expected
coerce-unseal-computation
    {expected = expected} lookup-eq refl (suc n)
    | yes refl =
  refl
coerce-unseal-computation
    {expected = expected} lookup-eq refl (suc n)
    | no expected≢expected =
  ⊥-elim (expected≢expected refl)

coerce-generalization-computation :
  ∀ {W θ A c V} n →
  coerceValue W θ (genᶜ A c) V n ≡
  immediateReturn W (generalized A c θ V) n
coerce-generalization-computation zero =
  refl
coerce-generalization-computation (suc n) =
  refl

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
coerce-instantiation-computation zero =
  refl
coerce-instantiation-computation {W} {θ} {B} {c} {V} (suc n)
    with instantiateValue
      (allocate W ★ θ) (freshSealName W) V n in head-eq
coerce-instantiation-computation {W} {θ} {B} {c} {V} (suc n)
    | timed U =
  refl
coerce-instantiation-computation {W} {θ} {B} {c} {V} (suc n)
    | blamed U =
  refl
coerce-instantiation-computation {W} {θ} {B} {c} {V} (suc n)
    | failed U e =
  refl
coerce-instantiation-computation {W} {θ} {B} {c} {V} (suc n)
    | returned U Q =
  refl
