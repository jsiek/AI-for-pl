module strong.RepresentationTypes where

-- Strong System F v8 — representation types and their ADDRESSES.
--
-- An address locates a representation type.  `lvl ℓ` is a stable level
-- into the global store Σ; the store is append-only, so levels are
-- never renamed.  `bnd i` is a de Bruijn index over the enclosing
-- address binders — `Λα,X`, `να:=R`, `∀ᴿ`, and the binder assignment
-- `X:α` pushed by the `∀` conversion element and the type-level `∀`
-- rules.  Only bound addresses ever shift.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Addr : Set where
  lvl : ℕ → Addr
  bnd : ℕ → Addr

lvl-inj : ∀ {ℓ m} → lvl ℓ ≡ lvl m → ℓ ≡ m
lvl-inj refl = refl

bnd-inj : ∀ {i j} → bnd i ≡ bnd j → i ≡ j
bnd-inj refl = refl

infix 4 _≟ᵃ_
_≟ᵃ_ : (α β : Addr) → Dec (α ≡ β)
lvl ℓ ≟ᵃ lvl m with ℓ ≟ m
lvl ℓ ≟ᵃ lvl m | yes refl = yes refl
lvl ℓ ≟ᵃ lvl m | no ne = no λ eq → ne (lvl-inj eq)
lvl ℓ ≟ᵃ bnd j = no λ ()
bnd i ≟ᵃ lvl m = no λ ()
bnd i ≟ᵃ bnd j with i ≟ j
bnd i ≟ᵃ bnd j | yes refl = yes refl
bnd i ≟ᵃ bnd j | no ne = no λ eq → ne (bnd-inj eq)

infixr 7 _⇒ᴿ_
infix 6 `∀ᴿ

data RepTy : Set where
  `ᵃ_  : Addr → RepTy
  `ℕᴿ  : RepTy
  `𝔹ᴿ  : RepTy
  _⇒ᴿ_ : RepTy → RepTy → RepTy
  `∀ᴿ  : RepTy → RepTy

------------------------------------------------------------------------
-- Renaming of BOUND addresses; levels are stable
------------------------------------------------------------------------

Renameᵇ : Set
Renameᵇ = ℕ → ℕ

renᵃ : Renameᵇ → Addr → Addr
renᵃ ρ (lvl ℓ) = lvl ℓ
renᵃ ρ (bnd i) = bnd (ρ i)

⇑ᵃ : Addr → Addr
⇑ᵃ = renᵃ suc

extᵇ : Renameᵇ → Renameᵇ
extᵇ ρ zero    = zero
extᵇ ρ (suc i) = suc (ρ i)

renameᴿ : Renameᵇ → RepTy → RepTy
renameᴿ ρ (`ᵃ α)   = `ᵃ renᵃ ρ α
renameᴿ ρ `ℕᴿ      = `ℕᴿ
renameᴿ ρ `𝔹ᴿ      = `𝔹ᴿ
renameᴿ ρ (R ⇒ᴿ S) = renameᴿ ρ R ⇒ᴿ renameᴿ ρ S
renameᴿ ρ (`∀ᴿ R)  = `∀ᴿ (renameᴿ (extᵇ ρ) R)

⇑ᴿ : RepTy → RepTy
⇑ᴿ = renameᴿ suc

------------------------------------------------------------------------
-- Substitution of bound addresses by addresses
------------------------------------------------------------------------
-- Instantiating a binder replaces a bound address VARIABLE by an
-- ADDRESS (typically a fresh level, at `Alloc`); representation types
-- are never substituted for address variables.

SubstAddr : Set
SubstAddr = ℕ → Addr

extsᵃ : SubstAddr → SubstAddr
extsᵃ σ zero    = bnd zero
extsᵃ σ (suc i) = ⇑ᵃ (σ i)

substAddr : SubstAddr → Addr → Addr
substAddr σ (lvl ℓ) = lvl ℓ
substAddr σ (bnd i) = σ i

substᴿ : SubstAddr → RepTy → RepTy
substᴿ σ (`ᵃ α)   = `ᵃ substAddr σ α
substᴿ σ `ℕᴿ      = `ℕᴿ
substᴿ σ `𝔹ᴿ      = `𝔹ᴿ
substᴿ σ (R ⇒ᴿ S) = substᴿ σ R ⇒ᴿ substᴿ σ S
substᴿ σ (`∀ᴿ R)  = `∀ᴿ (substᴿ (extsᵃ σ) R)

-- Instantiate the innermost bound address (a `∀ᴿ`'s, or a discharged
-- binder's) by β; the remaining bound indices shift down.
inst₀ : Addr → SubstAddr
inst₀ β zero    = β
inst₀ β (suc i) = bnd i

_[_]ᵇ : RepTy → Addr → RepTy
R [ β ]ᵇ = substᴿ (inst₀ β) R
