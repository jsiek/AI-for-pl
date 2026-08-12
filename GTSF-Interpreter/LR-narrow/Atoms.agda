module LR-narrow.Atoms where

-- File Charter:
--   * Defines step-indexed atoms indexed by live imprecision assumptions.
--   * Aligns atom environments exactly with `ImpCtx`.
--   * Provides the two binder lifts used by paired `∀` and precise-right `ν`.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; ⇑ᵢₐ
  ; ⇑ᴸᵢₐ
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import Interpreter using (Value)

StepIndexedRelation : Set₁
StepIndexedRelation = ℕ → Value → Value → Set

DownwardClosed : StepIndexedRelation → Set
DownwardClosed R = ∀ {n : ℕ} {Vᴵ Vᴾ : Value}
  → R (suc n) Vᴵ Vᴾ
  → R n Vᴵ Vᴾ

record Atom (assumption : ImpAssm) : Set₁ where
  constructor atom
  field
    relation : StepIndexedRelation
    relation-downward : DownwardClosed relation

open Atom public

record AtomHolds
    {assumption : ImpAssm} (a : Atom assumption)
    (n : ℕ) (Vᴵ Vᴾ : Value) : Set where
  constructor atom-holds
  field
    relation-holds : relation a n Vᴵ Vᴾ

open AtomHolds public

data AtomEnvironment : ImpCtx → Set₁ where
  []ᵃ : AtomEnvironment []

  _∷ᵃ_ : ∀ {assumption Φ}
    → Atom assumption
    → AtomEnvironment Φ
    → AtomEnvironment (assumption ∷ Φ)

infixr 5 _∷ᵃ_

lookup-atom : ∀ {assumption Φ}
  → assumption ∈ Φ
  → AtomEnvironment Φ
  → Atom assumption
lookup-atom (here refl) (a ∷ᵃ ρ) = a
lookup-atom (there assumption∈) (a ∷ᵃ ρ) =
  lookup-atom assumption∈ ρ

rename-atom : ∀ {assumption}
  → (rename : ImpAssm → ImpAssm)
  → Atom assumption
  → Atom (rename assumption)
rename-atom rename a =
  atom (relation a) (relation-downward a)

lift-both-atoms : ∀ {Φ}
  → AtomEnvironment Φ
  → AtomEnvironment (⇑ᵢ Φ)
lift-both-atoms []ᵃ = []ᵃ
lift-both-atoms (a ∷ᵃ ρ) =
  rename-atom ⇑ᵢₐ a ∷ᵃ lift-both-atoms ρ

lift-right-atoms : ∀ {Φ}
  → AtomEnvironment Φ
  → AtomEnvironment (⇑ᴸᵢ Φ)
lift-right-atoms []ᵃ = []ᵃ
lift-right-atoms (a ∷ᵃ ρ) =
  rename-atom ⇑ᴸᵢₐ a ∷ᵃ lift-right-atoms ρ
