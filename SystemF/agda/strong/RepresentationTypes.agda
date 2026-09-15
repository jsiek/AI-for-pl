module strong.RepresentationTypes where

-- Strong System F v8 — representation types and their ADDRESSES.
--
-- An address locates a representation type.  `lvl ℓ` is a stable level
-- into the global store Σ; the store is append-only, so levels are
-- never renamed.  The two BOUND forms mirror the two halves of a
-- context (`strong.Ctx`):
--
--   * `bnd i` indexes the STACK's binders — the binder assignment `X:α`
--     pushed by the `∀` conversion element, by `∀ᴿ`, and by the
--     type-level `∀` rules;
--   * `bse j` indexes the BASE's binders — a `Λ`'s address and a `ν`'s.
--
-- Keeping them apart is what makes both halves usable.  A `Λ`'s own
-- address is `bse zero` no matter how many crossings and `∀`s stand
-- above it, so the color wrap can WRITE it; and pushing a base binder
-- shifts `bse` alone, leaving every stack address — hence every
-- crossing, hence every pop — exactly as it was.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Addr : Set where
  lvl : ℕ → Addr
  bnd : ℕ → Addr
  bse : ℕ → Addr

lvl-inj : ∀ {ℓ m} → lvl ℓ ≡ lvl m → ℓ ≡ m
lvl-inj refl = refl

bnd-inj : ∀ {i j} → bnd i ≡ bnd j → i ≡ j
bnd-inj refl = refl

bse-inj : ∀ {i j} → bse i ≡ bse j → i ≡ j
bse-inj refl = refl

infix 4 _≟ᵃ_
_≟ᵃ_ : (α β : Addr) → Dec (α ≡ β)
lvl ℓ ≟ᵃ lvl m with ℓ ≟ m
lvl ℓ ≟ᵃ lvl m | yes refl = yes refl
lvl ℓ ≟ᵃ lvl m | no ne = no λ eq → ne (lvl-inj eq)
lvl ℓ ≟ᵃ bnd j = no λ ()
lvl ℓ ≟ᵃ bse j = no λ ()
bnd i ≟ᵃ lvl m = no λ ()
bnd i ≟ᵃ bse j = no λ ()
bse i ≟ᵃ lvl m = no λ ()
bse i ≟ᵃ bnd j = no λ ()
bnd i ≟ᵃ bnd j with i ≟ j
bnd i ≟ᵃ bnd j | yes refl = yes refl
bnd i ≟ᵃ bnd j | no ne = no λ eq → ne (bnd-inj eq)
bse i ≟ᵃ bse j with i ≟ j
bse i ≟ᵃ bse j | yes refl = yes refl
bse i ≟ᵃ bse j | no ne = no λ eq → ne (bse-inj eq)

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

-- A STACK renaming touches `bnd` alone: levels are stable, and so are
-- base addresses, which the stack's binders do not shift.
renᵃ : Renameᵇ → Addr → Addr
renᵃ ρ (lvl ℓ) = lvl ℓ
renᵃ ρ (bnd i) = bnd (ρ i)
renᵃ ρ (bse j) = bse j

-- A BASE renaming is the mirror image.
renᵃᵉ : Renameᵇ → Addr → Addr
renᵃᵉ ρ (lvl ℓ) = lvl ℓ
renᵃᵉ ρ (bnd i) = bnd i
renᵃᵉ ρ (bse j) = bse (ρ j)

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

-- `∀ᴿ binds a STACK address, so a base renaming passes through it
-- unextended.
renameᴿᵉ : Renameᵇ → RepTy → RepTy
renameᴿᵉ ρ (`ᵃ α)   = `ᵃ renᵃᵉ ρ α
renameᴿᵉ ρ `ℕᴿ      = `ℕᴿ
renameᴿᵉ ρ `𝔹ᴿ      = `𝔹ᴿ
renameᴿᵉ ρ (R ⇒ᴿ S) = renameᴿᵉ ρ R ⇒ᴿ renameᴿᵉ ρ S
renameᴿᵉ ρ (`∀ᴿ R)  = `∀ᴿ (renameᴿᵉ ρ R)

⇑ᴿᵉ : RepTy → RepTy
⇑ᴿᵉ = renameᴿᵉ suc

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
substAddr σ (bse j) = bse j

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

-- The BASE mirror: discharging a `ν` replaces its address, `bse zero`,
-- by the fresh store level.  `∀ᴿ` binds a stack address, so the
-- substitution passes through it unextended.
substAddrᵉ : SubstAddr → Addr → Addr
substAddrᵉ σ (lvl ℓ) = lvl ℓ
substAddrᵉ σ (bnd i) = bnd i
substAddrᵉ σ (bse j) = σ j

substᴿᵉ : SubstAddr → RepTy → RepTy
substᴿᵉ σ (`ᵃ α)   = `ᵃ substAddrᵉ σ α
substᴿᵉ σ `ℕᴿ      = `ℕᴿ
substᴿᵉ σ `𝔹ᴿ      = `𝔹ᴿ
substᴿᵉ σ (R ⇒ᴿ S) = substᴿᵉ σ R ⇒ᴿ substᴿᵉ σ S
substᴿᵉ σ (`∀ᴿ R)  = `∀ᴿ (substᴿᵉ σ R)

instᵉ₀ : Addr → SubstAddr
instᵉ₀ β zero    = β
instᵉ₀ β (suc j) = bse j

_[_]ᵉ : RepTy → Addr → RepTy
R [ β ]ᵉ = substᴿᵉ (instᵉ₀ β) R
