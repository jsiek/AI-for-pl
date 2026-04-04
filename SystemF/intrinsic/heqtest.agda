{-# OPTIONS --rewriting #-}

module intrinsic.heqtest where

open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

open import intrinsic.Types
open import intrinsic.Ctx
open import intrinsic.Terms

test0 : ∀ {Δ Γ} → substᵀ idᵗ (`zero {Δ = Δ} {Γ = Γ}) ≅ (`zero {Δ = Δ} {Γ = Γ})
test0 = refl

test1 : ∀ {Δ Γ A} (x : Γ ∋ A) → substᵗ-∋ idᵗ x ≅ x
test1 x = refl
