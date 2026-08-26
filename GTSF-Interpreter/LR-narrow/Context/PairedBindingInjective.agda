module LR-narrow.Context.PairedBindingInjective where

-- File Charter:
--   * Proves that a right seal has at most one paired left seal.
--   * Uses only the structural uniqueness certificate stored in an LR world.
--   * Contains exactly one exported theorem.

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import LR-narrow.Atoms using (StepIndexedRelation)
open import LR-narrow.World

private
  paired-binding-injectiveᵖ : ∀
      {entries α₁ α₂ α′}
      {R S : StepIndexedRelation}
    → BindingsUnique entries
    → entries ∋ α₁ ↔ α′ ∶ R
    → entries ∋ α₂ ↔ α′ ∶ S
    → α₁ ≡ α₂
  paired-binding-injectiveᵖ bindings-unique-empty () second
  paired-binding-injectiveᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      paired-here paired-here = refl
  paired-binding-injectiveᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      paired-here (paired-there second) = ⊥-elim (right-fresh second)
  paired-binding-injectiveᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      (paired-there first) paired-here = ⊥-elim (right-fresh first)
  paired-binding-injectiveᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      (paired-there first) (paired-there second) =
    paired-binding-injectiveᵖ unique first second
  paired-binding-injectiveᵖ
      (bindings-unique-right-dynamic unique)
      (paired-there first) (paired-there second) =
    paired-binding-injectiveᵖ unique first second

paired-binding-injective : ∀
    {w : World} {α₁ α₂ α′}
    {R S : StepIndexedRelation}
  → bindings w ∋ α₁ ↔ α′ ∶ R
  → bindings w ∋ α₂ ↔ α′ ∶ S
  → α₁ ≡ α₂
paired-binding-injective {w = w} =
  paired-binding-injectiveᵖ (bindings-unique w)
