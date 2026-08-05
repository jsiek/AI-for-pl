module proof.InterpreterWorldScopeProof where

-- File Charter:
--   * Projects related type environments to individually scoped ones.
--   * Proves that captured-environment scope survives world extension.
--   * Keeps scope recursion separate from correspondence algebra.

open import Interpreter
open import Narrowing.InterpreterWorldNarrowing
import proof.InterpreterWorldNarrowingProof as WorldProof
open import Types

module WorldScopeProof
  (TypeNarrowing : Ty → Ty → Set₁)
  where

  open WorldNarrowing TypeNarrowing
  module Correspondence = WorldProof.WorldNarrowingProof TypeNarrowing

  type-name-left-scoped :
    ∀ {W W′ X X′} {R : WorldRelation W W′} →
    TypeNameNarrowing R X X′ →
    TypeNameScoped W X
  type-name-left-scoped abstract-name⊑ =
    abstract-scoped
  type-name-left-scoped (seal-name⊑ α~α′) =
    seal-scoped (Correspondence.seal-link-left-allocated α~α′)

  type-name-right-scoped :
    ∀ {W W′ X X′} {R : WorldRelation W W′} →
    TypeNameNarrowing R X X′ →
    TypeNameScoped W′ X′
  type-name-right-scoped abstract-name⊑ =
    abstract-scoped
  type-name-right-scoped (seal-name⊑ α~α′) =
    seal-scoped (Correspondence.seal-link-right-allocated α~α′)

  type-environment-left-scoped :
    ∀ {W W′ θ θ′} {R : WorldRelation W W′} →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentScoped W θ
  type-environment-left-scoped []⊑[]ᵗᵉ =
    []-scoped
  type-environment-left-scoped (X~X′ ∷⊑∷ᵗᵉ θ~θ′) =
    type-name-left-scoped X~X′ ∷-scoped
      type-environment-left-scoped θ~θ′
  type-environment-left-scoped (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) =
    X-ok ∷-scoped type-environment-left-scoped θ~θ′
  type-environment-left-scoped (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) =
    type-environment-left-scoped θ~θ′

  type-environment-right-scoped :
    ∀ {W W′ θ θ′} {R : WorldRelation W W′} →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentScoped W′ θ′
  type-environment-right-scoped []⊑[]ᵗᵉ =
    []-scoped
  type-environment-right-scoped (X~X′ ∷⊑∷ᵗᵉ θ~θ′) =
    type-name-right-scoped X~X′ ∷-scoped
      type-environment-right-scoped θ~θ′
  type-environment-right-scoped (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) =
    type-environment-right-scoped θ~θ′
  type-environment-right-scoped (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) =
    X′-ok ∷-scoped type-environment-right-scoped θ~θ′

  type-environment-left-scope-weaken :
    ∀ {W W′ U U′ θ}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentScoped W θ →
    TypeEnvironmentScoped U θ
  type-environment-left-scope-weaken R≤S []-scoped =
    []-scoped
  type-environment-left-scope-weaken
      R≤S (abstract-scoped ∷-scoped θ-ok) =
    abstract-scoped ∷-scoped
      type-environment-left-scope-weaken R≤S θ-ok
  type-environment-left-scope-weaken
      R≤S (seal-scoped α∈W ∷-scoped θ-ok) =
    seal-scoped
      (Correspondence.allocated-left-weaken R≤S α∈W) ∷-scoped
      type-environment-left-scope-weaken R≤S θ-ok

  type-environment-right-scope-weaken :
    ∀ {W W′ U U′ θ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentScoped W′ θ′ →
    TypeEnvironmentScoped U′ θ′
  type-environment-right-scope-weaken R≤S []-scoped =
    []-scoped
  type-environment-right-scope-weaken
      R≤S (abstract-scoped ∷-scoped θ′-ok) =
    abstract-scoped ∷-scoped
      type-environment-right-scope-weaken R≤S θ′-ok
  type-environment-right-scope-weaken
      R≤S (seal-scoped α′∈W′ ∷-scoped θ′-ok) =
    seal-scoped
      (Correspondence.allocated-right-weaken R≤S α′∈W′) ∷-scoped
      type-environment-right-scope-weaken R≤S θ′-ok
