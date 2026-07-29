module InterpreterValueNarrowingExamples where

-- File Charter:
--   * Checks paired and one-sided world extension by normalization.
--   * Exercises seal correspondence, environment lookup, joined values, and
--     paired fresh-name substitution.
--   * Uses trivial Milestone-3 leaves to isolate the semantic structure.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Interpreter
import InterpreterEnvironmentNarrowing as EnvironmentProperties
import InterpreterJoined as JoinedDefinition
open import InterpreterValueNarrowing
import InterpreterValueSubstitution as Substitution
open import InterpreterWorldNarrowing
import InterpreterWorldNarrowingProperties as WorldProperties
open import Primitives using (κℕ)
open import Types

data Trivial : Set₁ where
  trivial : Trivial

trivialLeaves : NarrowingLeaves
trivialLeaves =
  record
    { BodyNarrowing = λ N N′ → Trivial
    ; TypeNarrowing = λ A A′ → Trivial
    ; GroundNarrowing = λ gG gH → Trivial
    ; CoercionNarrowing = λ c c′ → Trivial
    ; LeftTaggedBoundary = λ gG → Trivial
    ; RightTaggedBoundary = λ gH → Trivial
    ; LeftFunctionProxyBoundary = λ p q → Trivial
    ; RightFunctionProxyBoundary = λ p′ q′ → Trivial
    ; LeftForallProxyBoundary = λ c → Trivial
    ; RightForallProxyBoundary = λ c′ → Trivial
    ; LeftGeneralizationBoundary = λ A c → Trivial
    ; RightGeneralizationBoundary = λ A′ c′ → Trivial
    }

module Values = ValueNarrowing trivialLeaves
open Values
open Values.RelatedWorlds

module Environments =
  EnvironmentProperties.EnvironmentNarrowing trivialLeaves

module JoinedValues = JoinedDefinition.Joined trivialLeaves
module SubstitutionProof = Substitution.ValueSubstitution trivialLeaves

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    (TypeNarrowing trivialLeaves)

Nat : Ty
Nat = ‵ `ℕ

seven : Value
seven = constant (κℕ 7)

paired-worlds :
  WorldRelation
    (allocate emptyWorld Nat [])
    (allocate emptyWorld Nat [])
paired-worlds =
  allocate-both empty-world⊑ trivial []⊑[]ᵗᵉ

fresh-link :
  SealLink paired-worlds
    (seal-name-id zero)
    (seal-name-id zero)
fresh-link =
  link-here

fresh-link-functional :
  seal-name-id zero ≡ seal-name-id zero
fresh-link-functional =
  WorldProof.seal-link-functional fresh-link fresh-link

old-link-survives-left-allocation :
  SealLink
    (allocate-left-dynamic paired-worlds []-scoped)
    (seal-name-id zero)
    (seal-name-id zero)
old-link-survives-left-allocation =
  link-under-left fresh-link

environment-lookup-example :
  Σ[ V′ ∈ Value ]
    lookup (seven ∷ []) zero ≡ just V′ ×
    ValueNarrowing empty-world⊑ seven V′
environment-lookup-example =
  Environments.environment-lookup-narrowing {x = zero}
    (constant⊑ (κℕ 7) ∷⊑∷ᵉ []⊑[]ᵉ) refl

sealed-values-joined :
  JoinedValues.Joined
    (allocate emptyWorld Nat [])
    (sealed (seal-name-id zero) seven)
    (allocate emptyWorld Nat [])
    (sealed (seal-name-id zero) seven)
sealed-values-joined =
  JoinedValues.joined
    (paired-worlds ,
      sealed⊑ fresh-link (constant⊑ (κℕ 7)))

abstractZero : Name
abstractZero = type-name zero

tagged-abstract-values :
  ValueNarrowing empty-world⊑
    (tagged (‵ `ℕ) (abstract-name abstractZero ∷ []) seven)
    (tagged (‵ `ℕ) (abstract-name abstractZero ∷ []) seven)
tagged-abstract-values =
  tagged⊑ trivial
    (abstract-name⊑ ∷⊑∷ᵗᵉ []⊑[]ᵗᵉ)
    (constant⊑ (κℕ 7))

substitution-example :
  ValueNarrowing paired-worlds
    (tagged (‵ `ℕ) (seal-name (seal-name-id zero) ∷ []) seven)
    (tagged (‵ `ℕ) (seal-name (seal-name-id zero) ∷ []) seven)
substitution-example =
  SubstitutionProof.substitute-name-preserves-value-narrowing
    {X = abstractZero}
    trivial []⊑[]ᵗᵉ tagged-abstract-values
