module Examples.InterpreterLeftTypeAbstractionNarrowingExamples where

-- File Charter:
--   * Exercises source-only abstraction instantiation with an occurring name.
--   * Checks that the abstract captured name becomes the fresh dynamic seal.
--   * Uses trivial leaves to isolate the extensional certificate.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero)

open import Interpreter
import Narrowing.InterpreterLeftTypeAbstractionNarrowing as
  AbstractionDefinition
open import Examples.InterpreterNarrowingTestLeaves
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
open import Primitives using (κℕ)
open import Types

module Values = ValueNarrowing trivialLeaves
open Values
open Values.RelatedWorlds

module Abstractions =
  AbstractionDefinition.LeftTypeAbstractionNarrowing trivialLeaves

Nat : Ty
Nat =
  ‵ `ℕ

binder : Name
binder =
  type-name zero

seven : Value
seven =
  constant (κℕ 7)

source-body : Value
source-body =
  tagged (‵ `ℕ) (abstract-name binder ∷ []) seven

left-abstraction-certificate :
  LeftTypeAbstractionNarrowing
    empty-world⊑ binder source-body seven
left-abstraction-certificate =
  related-left-type-abstraction
    (tagged-scoped
      (abstract-scoped ∷-scoped []-scoped)
      constant-scoped)
    constant-scoped
    (λ R≤S σ-ok →
      left-tagged⊑ trivial
        (seal-scoped (allocated (here refl)) ∷-scoped []-scoped)
        (constant⊑ (κℕ 7)))

left-worlds :
  WorldRelation (allocate emptyWorld Nat []) emptyWorld
left-worlds =
  allocate-left-dynamic {A = Nat} empty-world⊑ []-scoped

instantiated-left-body :
  ValueNarrowing left-worlds
    (tagged (‵ `ℕ)
      (seal-name (seal-name-id zero) ∷ []) seven)
    seven
instantiated-left-body =
  Abstractions.instantiate-related-left-type-abstraction
    left-abstraction-certificate extension-refl []-scoped
