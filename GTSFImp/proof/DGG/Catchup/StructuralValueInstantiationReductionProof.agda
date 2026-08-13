module
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof where

-- File Charter:
--   * Lifts one allocating reduction through a typed pending spine.
--   * Maps every surrounding frame across the fresh binding.

open import Data.Nat using (suc)
open import Types using (Ty)
open import CastTerms using (Term)
open import Relation.Binary.PropositionalEquality using (refl)
open import Reduction using
  (bind; _—→[_]_; ξ-•; ξ-⟨⟩; ξ-reveal; ξ-conceal)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


lift-instantiation-frame-bind : ∀ {Δ A B}
    {M : Term Δ} {M′ : Term (suc Δ)} {R : Ty Δ}
  → M —→[ bind R ] M′
  → (frame : InstantiationFrame A B)
  → applyInstantiationFrame M frame —→[ bind R ]
      applyInstantiationFrame M′ (mapInstantiationFrame (bind R) frame)
lift-instantiation-frame-bind step (type-transport-frame eq) = step
lift-instantiation-frame-bind step
    (name-type-app-frame B X eqA eqC) =
  ξ-• step refl refl
lift-instantiation-frame-bind step (cast-frame c) =
  ξ-⟨⟩ step refl
lift-instantiation-frame-bind step (reveal-frame c) =
  ξ-reveal step refl
lift-instantiation-frame-bind step (conceal-frame c) =
  ξ-conceal step refl


lift-instantiation-spine-bind : ∀ {Δ A B}
    {M : Term Δ} {M′ : Term (suc Δ)} {R : Ty Δ}
  → M —→[ bind R ] M′
  → (spine : InstantiationSpine A B)
  → applyInstantiationSpine M spine —→[ bind R ]
      applyInstantiationSpine M′
        (mapInstantiationSpine (bind R) spine)
lift-instantiation-spine-bind step []ⁱ = step
lift-instantiation-spine-bind step (frame ▻ⁱ spine) =
  lift-instantiation-spine-bind
    (lift-instantiation-frame-bind step frame) spine
