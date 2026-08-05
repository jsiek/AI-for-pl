module Simulation.Polymorphism.InterpreterForallPermutationPath where

-- File Charter:
--   * Public interface for normalized oriented `∀`-permutation paths.
--   * Exposes normalization and a structurally recursive path eliminator.
--   * Projects the normalized path retained by a compiler representative
--     alignment without recomputing endpoint enumeration.
--   * Delegates proofs to `proof.InterpreterForallPermutationPathProof`.

open import ForallPermutation using (_≈∀_)
open import
  Simulation.Polymorphism.InterpreterForallPermutationPathDefinition public
open import proof.EndpointCanonicalMLBSimplePermutation using
  (aligned-routes-≈∀)
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (EndpointRepresentativeAlignment; route-alignment)
open import Types using (Ty)
open import proof.InterpreterForallPermutationPathProof as Proof


normalize-forall-permutation :
  ∀ {A B} →
  A ≈∀ B →
  A ≈∀ⁿ B
normalize-forall-permutation =
  Proof.normalize-forall-permutation-proof


endpoint-representative-path :
  ∀ {Δ X Y E D′} →
  EndpointRepresentativeAlignment Δ X Y E D′ →
  E ≈∀ⁿ D′
endpoint-representative-path alignment =
  normalize-forall-permutation
    (aligned-routes-≈∀ (route-alignment alignment))


fold-forall-permutation-path :
  (P : Ty → Ty → Set₁) →
  ((A : Ty) → P A A) →
  (∀ {A B C} → A ↝∀ B → P B C → P A C) →
  ∀ {A B} →
  A ≈∀ⁿ B →
  P A B
fold-forall-permutation-path =
  Proof.fold-forall-permutation-path-proof
