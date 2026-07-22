module proof.NuImprecisionAssumptionMembershipUniquenessDef where

-- File Charter:
--   * Defines proof-relevant uniqueness of imprecision assumptions.
--   * Defines uniqueness of well-formed type-imprecision indices.
--   * States the higher-order bridge from assumption uniqueness to index
--     uniqueness, parameterized by fresh-path transport.
--   * Contains no implementation, simulation carrier, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)

open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import proof.NuImprecisionFreshTypePathImprecisionTransportDef using
  (FreshTypePathImprecisionTransport)


AssumptionMembershipUnique : ImpCtx → Set
AssumptionMembershipUnique Φ =
  ∀ {a : ImpAssm} (i j : a ∈ Φ) → i ≡ j


PrecisionIndexUnique : ImpCtx → Set
PrecisionIndexUnique Φ =
  ∀ {Δᴸ Δᴿ A B}
    (p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  p ≡ q


AssumptionMembershipUniquenessᵀ : Set
AssumptionMembershipUniquenessᵀ =
  FreshTypePathImprecisionTransport →
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  PrecisionIndexUnique Φ
