module Examples.InterpreterTypeAbstractionNarrowingExamples where

-- File Charter:
--   * Checks alpha-aware paired type abstractions with distinct binder names.
--   * Exercises direct paired instantiation and a nested abstraction whose
--     binder-name supplies remain offset on the two sides.
--   * Uses trivial leaves so normalization tests only the nominal structure.

open import Data.List using ([])
open import Data.Nat using (zero; suc)

open import Interpreter
open import Examples.InterpreterNarrowingTestLeaves
import Narrowing.InterpreterTypeAbstractionNarrowing as AbstractionDefinition
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
open import Primitives using (κℕ)
open import Types

module Values = ValueNarrowing trivialLeaves
open Values
open Values.RelatedWorlds

module Abstractions =
  AbstractionDefinition.TypeAbstractionNarrowing trivialLeaves

Nat : Ty
Nat = ‵ `ℕ

seven : Value
seven = constant (κℕ 7)

leftOuter : Name
leftOuter = type-name zero

rightOuter : Name
rightOuter = type-name (suc zero)

leftInner : Name
leftInner = type-name (suc zero)

rightInner : Name
rightInner = type-name (suc (suc zero))

paired-worlds :
  WorldRelation
    (allocate emptyWorld Nat [])
    (allocate emptyWorld Nat [])
paired-worlds =
  allocate-both empty-world⊑ trivial []⊑[]ᵗᵉ

distinct-name-certificate :
  TypeAbstractionNarrowing
    empty-world⊑ leftOuter rightOuter seven seven
distinct-name-certificate =
  related-type-abstraction constant-scoped constant-scoped
    (λ R≤S A~A′ θ~θ′ → constant⊑ (κℕ 7))

distinct-name-abstractions :
  ValueNarrowing empty-world⊑
    (type-abstraction leftOuter seven)
    (type-abstraction rightOuter seven)
distinct-name-abstractions =
  type-abstraction⊑ distinct-name-certificate

distinct-name-instantiation :
  ValueNarrowing paired-worlds seven seven
distinct-name-instantiation =
  Abstractions.instantiate-related-type-abstraction
    distinct-name-certificate trivial []⊑[]ᵗᵉ

nested-offset-certificate :
  TypeAbstractionNarrowing empty-world⊑ leftOuter rightOuter
    (type-abstraction leftInner seven)
    (type-abstraction rightInner seven)
nested-offset-certificate =
  related-type-abstraction
    (type-abstraction-scoped constant-scoped)
    (type-abstraction-scoped constant-scoped)
    (λ R≤S A~A′ θ~θ′ →
      type-abstraction⊑
        (related-type-abstraction constant-scoped constant-scoped
          (λ S≤T B~B′ σ~σ′ → constant⊑ (κℕ 7))))

nested-offset-instantiation :
  ValueNarrowing paired-worlds
    (type-abstraction leftInner seven)
    (type-abstraction rightInner seven)
nested-offset-instantiation =
  Abstractions.instantiate-related-type-abstraction
    nested-offset-certificate trivial []⊑[]ᵗᵉ
