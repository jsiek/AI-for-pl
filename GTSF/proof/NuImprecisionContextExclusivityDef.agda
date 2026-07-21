module proof.NuImprecisionContextExclusivityDef where

-- File Charter:
--   * Defines source-name exclusivity for imprecision contexts.
--   * Rules out assigning one source type name both a source-only row and a
--     matched source/target row.
--   * Contains no preservation proofs or simulation dependencies.

open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)

open import Imprecision using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_)


SourceNameExclusive : ImpCtx → Set
SourceNameExclusive Φ =
  ∀ {α β} →
  (α ˣ⊑★) ∈ Φ →
  (α ˣ⊑ˣ β) ∈ Φ →
  ⊥
