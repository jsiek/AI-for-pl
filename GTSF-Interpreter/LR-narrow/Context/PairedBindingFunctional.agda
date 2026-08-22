module LR-narrow.Context.PairedBindingFunctional where

-- File Charter:
--   * Proves that a left seal has at most one paired right seal.
--   * Uses only the structural uniqueness certificate stored in an LR world.
--   * Contains exactly one exported theorem.

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import LR-narrow.Atoms using (StepIndexedRelation)
open import LR-narrow.World

private
  paired-binding-functionalᵖ : ∀
      {entries α α₁′ α₂′}
      {R S : StepIndexedRelation}
    → BindingsUnique entries
    → entries ∋ α ↔ α₁′ ∶ R
    → entries ∋ α ↔ α₂′ ∶ S
    → α₁′ ≡ α₂′
  paired-binding-functionalᵖ bindings-unique-empty () second
  paired-binding-functionalᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      paired-here paired-here = refl
  paired-binding-functionalᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      paired-here (paired-there second) = ⊥-elim (left-fresh second)
  paired-binding-functionalᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      (paired-there first) paired-here = ⊥-elim (left-fresh first)
  paired-binding-functionalᵖ
      (bindings-unique-paired left-fresh right-fresh unique)
      (paired-there first) (paired-there second) =
    paired-binding-functionalᵖ unique first second
  paired-binding-functionalᵖ
      (bindings-unique-right-dynamic unique)
      (paired-there first) (paired-there second) =
    paired-binding-functionalᵖ unique first second

paired-binding-functional : ∀
    {w : World} {α α₁′ α₂′}
    {R S : StepIndexedRelation}
  → bindings w ∋ α ↔ α₁′ ∶ R
  → bindings w ∋ α ↔ α₂′ ∶ S
  → α₁′ ≡ α₂′
paired-binding-functional {w = w} =
  paired-binding-functionalᵖ (bindings-unique w)
