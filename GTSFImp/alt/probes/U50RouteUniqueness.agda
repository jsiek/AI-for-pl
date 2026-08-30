{-# OPTIONS --allow-unsolved-metas #-}

module alt.probes.U50RouteUniqueness where

-- File Charter:
--   * States route coherence for the telescope-indexed ScopeRoute.
--   * The former seven constructor holes collapse to one genuine coherence
--     obligation: scope-target can compose an arbitrary TypingTarget, so the
--     structural proof needs uniqueness of TypingTarget's regular injection.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Consistency
open import alt.ThetaTyping

scopeRoute-pointwise : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
    {birth : TyEnv Θ₀ Δ₀ σ₀} {stage : TyEnv Θ Δ σ}
    {ρ η : Δ₀ ↪ᵗ Δ}
  → ScopeRoute birth stage ρ
  → ScopeRoute birth stage η
  → ∀ X → toRenameᵗ ρ X ≡ toRenameᵗ η X
scopeRoute-pointwise left right X = ?
