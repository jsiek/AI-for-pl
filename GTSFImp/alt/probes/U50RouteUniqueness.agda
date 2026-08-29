{-# OPTIONS --allow-unsolved-metas #-}

module alt.probes.U50RouteUniqueness where

open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

open import Types
open import Consistency
open import alt.ThetaTyping

scopeRoute-pointwise : ∀ {birthΔ Δ}
    {birth : BirthScope birthΔ} {stage : StageEnv Δ}
    {ρ η : birthΔ ↪ᵗ Δ}
  → (left : ScopeRoute birth stage ρ)
  → (right : ScopeRoute birth stage η)
  → ∀ X → toRenameᵗ ρ X ≡ toRenameᵗ η X
scopeRoute-pointwise (scope-here source-id) right X =
  trans (source-id X) (sym (same-injection-pointwise _ X))
scopeRoute-pointwise (scope-ν left) (scope-here x) X = ?
scopeRoute-pointwise (scope-ν left) (scope-ν right) X = ?
scopeRoute-pointwise (scope-ν left) (scope-target right x x₁ x₂) X = ?
scopeRoute-pointwise (scope-typ left) right X = ?
scopeRoute-pointwise (scope-begin left x) right X = ?
scopeRoute-pointwise (scope-end left x) right X = ?
scopeRoute-pointwise (scope-target left x x₁ x₂) right X = ?
