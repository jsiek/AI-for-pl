module proof.Core.Equality.HeterogeneousEqualityTransport where

-- File Charter:
--   * Provides the reusable heterogeneous equalities produced by transporting
--     a proof along one or two propositional endpoint equalities.
--   * Contains no language, simulation, store, or quotient-specific result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)
import Relation.Binary.HeterogeneousEquality as HE

subst-to-≅ :
  ∀ {A : Set} {P : A → Set} {x y : A} →
  (eq : x ≡ y) →
  (p : P x) →
  HE._≅_ (subst P eq p) p
subst-to-≅ refl p = HE.refl

subst²-to-≅ :
  ∀ {A B : Set} {P : A → B → Set}
    {x₀ x₁ : A} {y₀ y₁ : B} →
  (x₀≡x₁ : x₀ ≡ x₁) →
  (y₀≡y₁ : y₀ ≡ y₁) →
  (p : P x₀ y₀) →
  HE._≅_
    (subst (P x₁) y₀≡y₁
      (subst (λ x → P x y₀) x₀≡x₁ p))
    p
subst²-to-≅ refl refl p = HE.refl
