module proof.NuImprecisionCorrespondingSourceNameNotStarDef where

-- File Charter:
--   * Defines the reusable world-invariant corollary that a source name in a
--     live matched correspondence cannot also be source-only.
--   * Exposes the exact correspondence and source-only context witnesses.
--   * Contains no implementation, postulate, hole, permissive option, term
--     imprecision, or simulation import.

open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import ImprecisionWf using (_ˣ⊑★)
open import NuTermImprecision using (StoreCorresponds; StoreImp)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


CorrespondingSourceNameNotStarᵀ : Set₁
CorrespondingSourceNameNotStarᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {α β X X′ p} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreCorresponds ρ α X β X′ p →
  (α ˣ⊑★) ∈ Φ →
  ⊥
