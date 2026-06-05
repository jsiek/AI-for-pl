module CoercionNormalization where

-- File Charter:
--   * Public bridge between coercions and quotiented coercions.
--   * Exposes the shared bridge vocabulary plus audit-facing round-trip and
--     normalization statements.
--   * Private proof implementation lives in `proof/CoercionNormalization.agda`.

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ-syntax; _×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Coercions
open import CoercionNormalizationDefinitions public
import CoercionReduction as Quot
import proof.CoercionNormalization as Proof

quotiented→coercion-roundtrip : ∀ {c A B}
  → (cwt : Quot.⊢_⦂_⇨_ c A B)
  → coercion→quotiented (proj₁ (quotiented→coercion cwt)) ≡ c
quotiented→coercion-roundtrip =
  Proof.quotiented→coercion-roundtrip

coercion-quotiented-roundtrip : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → TypedCoercionEq A B c
      (proj₁ (quotiented→coercion (coercion→quotiented-wt cwt)))
coercion-quotiented-roundtrip =
  Proof.coercion-quotiented-roundtrip

normalization : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Σ[ d ∈ Coercion ] (c —↠≈ᶜʳ d × Irreducible d)
normalization = Proof.normalization

coercion→quotiented-coerce : ∀ {A B}
  → (ℓ : Nat)
  → (p : A ~ B)
  → coercion→quotiented (coerce ℓ p) ≡ Quot.coerce ℓ p
coercion→quotiented-coerce =
  Proof.coercion→quotiented-coerce
