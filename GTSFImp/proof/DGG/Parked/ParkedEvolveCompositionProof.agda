module proof.DGG.Parked.ParkedEvolveCompositionProof where

-- File Charter:
--   * Proves transitive composition for parked-world evolution.
--   * Recurses only over the first evolution witness.
--   * Exports the completed composition lemma used by multi-step simulation.

open import proof.DGG.Parked.ParkedWorldDef using
  ( evolve-both-bind
  ; evolve-keepᴸ
  ; evolve-keepᴿ
  ; evolve-left-bind
  ; evolve-refl
  ; evolve-right-bind
  ; evolve-structural-right-bind
  )
open import proof.DGG.Parked.ParkedEvolveCompositionDef
  using (ComposeParkedEvolveᵀ)


compose-parked-evolve : ComposeParkedEvolveᵀ
compose-parked-evolve evolve-refl evol₂ = evol₂
compose-parked-evolve (evolve-keepᴸ evol₁) evol₂ =
  evolve-keepᴸ (compose-parked-evolve evol₁ evol₂)
compose-parked-evolve (evolve-keepᴿ evol₁) evol₂ =
  evolve-keepᴿ (compose-parked-evolve evol₁ evol₂)
compose-parked-evolve (evolve-both-bind evol₁) evol₂ =
  evolve-both-bind (compose-parked-evolve evol₁ evol₂)
compose-parked-evolve (evolve-left-bind evol₁) evol₂ =
  evolve-left-bind (compose-parked-evolve evol₁ evol₂)
compose-parked-evolve (evolve-right-bind evol₁) evol₂ =
  evolve-right-bind (compose-parked-evolve evol₁ evol₂)
compose-parked-evolve
    (evolve-structural-right-bind ins follows evol₁) evol₂ =
  evolve-structural-right-bind ins follows
    (compose-parked-evolve evol₁ evol₂)
